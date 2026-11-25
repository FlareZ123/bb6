import Raw39CounterCarry
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent11CounterCarry
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39RCCounter1089
namespace M1089

namespace MInit

-- 1RB0RC_1RC1LE_0RD1LE_1LD0RA_1LF0LE_0LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 3 ⟨4,[],(rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])⟩ = some ⟨2,([false,true]),([true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨2,([false]) ++ (L),([true]) ++ ([true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([false,false,false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨2,([false,true]),([true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])⟩ = some ⟨2,([false]) ++ (rep [false,false,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true] [true,false,true] [false,false,false] 3 local1 n (([true])) (([true,false,true,true,false,true,true,false,true,false,true,true,true,true,true]))

theorem phase2 (n : Nat) : run0 table 16 ⟨2,([false]) ++ (rep [false,false,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])⟩ = some ⟨1,([false,false,false,false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]),([false,true,false,true,true,true,true,true])⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]) = (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,false,false,true]) := by
  calc
    _ = ([false,false,false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false,false,false,false])) (([true])) [false,false] false n
    _ = ([false,false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false,false,false])) (([false,true])) [false,false] false n
    _ = ([false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false,false])) (([false,false,true])) [false,false] false n
    _ = ([false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false])) (([false,false,false,true])) [false,false] false n
    _ = ([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false])) (([false,false,false,false,true])) [false,false] false n
    _ = ([false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false])) (([false,false,false,false,false,true])) [false,false] false n
    _ = ([false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,false,false,false,false,false,true])) [false,false] false n
    _ = ([false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,false,false,false,false,false,true])) [false,false] false n
    _ = (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,false,false,false,false,false,false,false,true])) [false,false] false n

theorem finalR (n : Nat) : ([false,true,false,true,true,true,true,true]) = ([false,true,false,true,true,true,true,true]) := by
  rfl

theorem epoch (n : Nat) : run0 table (19+3*n) ⟨4,[],(rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])⟩ = some ⟨1,(rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,false,false,true]),([false,true,false,true,true,true,true,true])⟩ := by
  have H := (join0 (join0 (phase0 n) (phase1 n)) (phase2 n))
  rw [finalL n] at H
  rw [show 3+3*n+16=19+3*n by omega] at H
  exact H

theorem canon (n : Nat) : run0 table (19+3*n) ⟨4,[],(rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])⟩ = some ⟨1,(rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,false,false,true]),([false,true,false,true,true,true,true,true])⟩ := by
  exact epoch n

end MInit


namespace MFinish

-- 1RB0RC_1RC1LE_0RD1LE_1LD0RA_1LF0LE_0LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

theorem local0 (L R : List Bool) : run0 table 3 ⟨1,([true,false,false]) ++ (L),(R)⟩ = some ⟨1,(L),([false,true,true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (3*n) ⟨1,(rep [true,false,false] (n)) ++ ([true,false,false,true,false,false,true,false,false,true]),([false,true,false,true,true,true,true,true])⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false,true]),(rep [false,true,true] (n)) ++ ([false,true,false,true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [] [] [true,false,false] [false,true,true] 3 local0 n (([true,false,false,true,false,false,true,false,false,true])) (([false,true,false,true,true,true,true,true]))

theorem phase1 (n : Nat) : run0 table 10 ⟨1,([true,false,false,true,false,false,true,false,false,true]),(rep [false,true,true] (n)) ++ ([false,true,false,true,true,true,true,true])⟩ = some ⟨4,[],([true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,false,true,true,true,true,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,false,true,true,true,true,true]) = (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,true]) := by
  calc
    _ = ([true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,false,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,true,false,true,true,false,true])) (([false,true,false,true,true,true,true,true])) [false,true] true n
    _ = ([true,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true,true,false,true,false,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,true,false,true,true,false])) (([true,false,true,false,true,true,true,true,true])) [true,false] true n
    _ = ([true,false,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,false,true,false,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,true,false,true,true])) (([true,true,false,true,false,true,true,true,true,true])) [true,true] false n
    _ = ([true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,false,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,true,false,true])) (([false,true,true,false,true,false,true,true,true,true,true])) [false,true] true n
    _ = ([true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true,true,false,true,true,false,true,false,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,true,false])) (([true,false,true,true,false,true,false,true,true,true,true,true])) [true,false] true n
    _ = ([true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,false,true,true,false,true,false,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,true])) (([true,true,false,true,true,false,true,false,true,true,true,true,true])) [true,true] false n
    _ = ([true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,true,false,true,false,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true])) (([false,true,true,false,true,true,false,true,false,true,true,true,true,true])) [false,true] true n
    _ = ([true,false]) ++ (rep [true,true,false] (n)) ++ ([true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false])) (([true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])) [true,false] true n
    _ = ([true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true])) (([true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])) [true,true] false n
    _ = (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])) [false,true] true n

theorem epoch (n : Nat) : run0 table (10+3*n) ⟨1,(rep [true,false,false] (n)) ++ ([true,false,false,true,false,false,true,false,false,true]),([false,true,false,true,true,true,true,true])⟩ = some ⟨4,[],(rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])⟩ := by
  have H := (join0 (phase0 n) (phase1 n))
  rw [finalR n] at H
  rw [show 3*n+10=10+3*n by omega] at H
  exact H

theorem eq1r (n : Nat) : (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,true]) = ([true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,true,false,true,false,true,true,true,true,true]) := by
  calc
    _ = ([true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])) [false,true] true n
    _ = ([true,false]) ++ (rep [true,true,false] (n)) ++ ([true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true])) (([true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])) [true,true] false n
    _ = ([true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,true,false,true,false,true,true,true,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false])) (([true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])) [true,false] true n

theorem canon (n : Nat) : run0 table (10+3*n) ⟨1,(rep [true,false,false] (n)) ++ ([true,false,false,true,false,false,true,false,false,true]),([false,true,false,true,true,true,true,true])⟩ = some ⟨4,[],([true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])⟩ := by
  simpa only [eq1r n] using epoch n

end MFinish


namespace MCarry

-- 1RB0RC_1RC1LE_0RD1LE_1LD0RA_1LF0LE_0LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

theorem local0 (L R : List Bool) : run0 table 3 ⟨1,([true,false,false]) ++ (L),(R)⟩ = some ⟨1,(L),([false,true,true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) (R : List Bool) : run0 table (3*n) ⟨1,(rep [true,false,false] (n)) ++ ([true,false,false,false,false,false]) ++ (R),([false,true,false,true,true,true,true,true])⟩ = some ⟨1,([true,false,false,false,false,false]) ++ (R),(rep [false,true,true] (n)) ++ ([false,true,false,true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [] [] [true,false,false] [false,true,true] 3 local0 n (([true,false,false,false,false,false]) ++ (R)) (([false,true,false,true,true,true,true,true]))

theorem phase1 (n : Nat) (R : List Bool) : run0 table 4 ⟨1,([true,false,false,false,false,false]) ++ (R),(rep [false,true,true] (n)) ++ ([false,true,false,true,true,true,true,true])⟩ = some ⟨2,([false,true,false,false]) ++ (R),([true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,false,true,true,true,true,true])⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 3 ⟨2,([false]) ++ (L),([true,true]) ++ ([false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([false,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) (R : List Bool) : run0 table (3*n) ⟨2,([false,true,false,false]) ++ (R),([true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,false,true,true,true,true,true])⟩ = some ⟨2,([false]) ++ (rep [false,false,false] (n)) ++ ([true,false,false]) ++ (R),([true,true,false,true,false,true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true] [false,true,true] [false,false,false] 3 local2 n (([true,false,false]) ++ (R)) (([false,true,false,true,true,true,true,true]))

theorem phase3 (n : Nat) (R : List Bool) : run0 table 10 ⟨2,([false]) ++ (rep [false,false,false] (n)) ++ ([true,false,false]) ++ (R),([true,true,false,true,false,true,true,true,true,true])⟩ = some ⟨1,([false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,false,false]) ++ (R),([false,true,false,true,true,true,true,true])⟩ := by rfl

theorem finalL (n : Nat) (R : List Bool) : ([false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,false,false]) ++ (R) = (rep [false,false,false] (n)) ++ ([false,false,false,true,false,false]) ++ (R) := by
  calc
    _ = ([false,false]) ++ (rep [false,false,false] (n)) ++ ([false,true,false,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([true,false,false]) ++ (R)) [false,false] false n
    _ = ([false]) ++ (rep [false,false,false] (n)) ++ ([false,false,true,false,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,true,false,false]) ++ (R)) [false,false] false n
    _ = (rep [false,false,false] (n)) ++ ([false,false,false,true,false,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,false,true,false,false]) ++ (R)) [false,false] false n

theorem finalR (n : Nat) (R : List Bool) : ([false,true,false,true,true,true,true,true]) = ([false,true,false,true,true,true,true,true]) := by
  rfl

theorem epoch (n : Nat) (R : List Bool) : run0 table (14+6*n) ⟨1,(rep [true,false,false] (n)) ++ ([true,false,false,false,false,false]) ++ (R),([false,true,false,true,true,true,true,true])⟩ = some ⟨1,(rep [false,false,false] (n)) ++ ([false,false,false,true,false,false]) ++ (R),([false,true,false,true,true,true,true,true])⟩ := by
  have H := (join0 (join0 (join0 (phase0 n R) (phase1 n R)) (phase2 n R)) (phase3 n R))
  rw [finalL n R] at H
  rw [show 3*n+4+3*n+10=14+6*n by omega] at H
  exact H

theorem canon (n : Nat) (R : List Bool) : run0 table (14+6*n) ⟨1,(rep [true,false,false] (n)) ++ ([true,false,false,false,false,false]) ++ (R),([false,true,false,true,true,true,true,true])⟩ = some ⟨1,(rep [false,false,false] (n)) ++ ([false,false,false,true,false,false]) ++ (R),([false,true,false,true,true,true,true,true])⟩ := by
  exact epoch n R

end MCarry


abbrev table := MInit.table
abbrev A : List Bool := [true,false,false]
abbrev Z : List Bool := [false,false,false]
def Q (R : List Bool) : Z0 := ⟨1,(R),[false,true,false,true,true,true,true,true]⟩
def family (n : Nat) : Z0 := ⟨4,[],(rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])⟩
def carryCost (n : Nat) : Nat := 8+6*n

theorem carry (n : Nat) (R : List Bool) : run0 table (carryCost n) (Q (rep A n ++ Z ++ R)) = some (Q (rep Z n ++ A ++ R)) := by
  cases n with
  | zero => rfl
  | succ n =>
    have h := MCarry.canon n R
    rw [show MCarry.table = table from rfl] at h
    unfold carryCost
    rw [show 8+6*n.succ = 14+6*n by omega]
    rw [rep_succ_snoc A n,rep_succ_snoc Z n]
    simpa only [table,Q,A,Z,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem entry : run0 table 116 ⟨0,[],[]⟩ = some (family 0) := by rfl


def cost (n : Nat) : Nat := (19+3*n) + fillCost carryCost (n+3) + (10+3*n)

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := MInit.canon n
  have h2 := fill table Q A Z carryCost carry (n+3) [true]
  have h3 := MFinish.canon n
  rw [rep_add Z n 3,rep_add A n 3] at h2
  simp only [Q,A,Z,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] at h2
  have h := join0 (join0 h1 h2) h3
  simpa only [cost,family,rep,rep_succ_snoc,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 116 cost entry (by intro n; unfold cost; omega) growth m hm

#print axioms growth
#print axioms never
end M1089
namespace M1399

namespace MInit

-- 1RB0RC_1RC1LF_0RD1LF_1LD0RA_0LB---_1LE0LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 3 ⟨5,[],(rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])⟩ = some ⟨2,([false,true]),([true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨2,([false]) ++ (L),([true]) ++ ([true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([false,false,false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨2,([false,true]),([true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])⟩ = some ⟨2,([false]) ++ (rep [false,false,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true] [true,false,true] [false,false,false] 3 local1 n (([true])) (([true,false,true,true,false,true,true,false,true,false,true,true,true,true,true]))

theorem phase2 (n : Nat) : run0 table 16 ⟨2,([false]) ++ (rep [false,false,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])⟩ = some ⟨1,([false,false,false,false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]),([false,true,false,true,true,true,true,true])⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]) = (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,false,false,true]) := by
  calc
    _ = ([false,false,false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false,false,false,false])) (([true])) [false,false] false n
    _ = ([false,false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false,false,false])) (([false,true])) [false,false] false n
    _ = ([false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false,false])) (([false,false,true])) [false,false] false n
    _ = ([false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false])) (([false,false,false,true])) [false,false] false n
    _ = ([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false])) (([false,false,false,false,true])) [false,false] false n
    _ = ([false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false])) (([false,false,false,false,false,true])) [false,false] false n
    _ = ([false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,false,false,false,false,false,true])) [false,false] false n
    _ = ([false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,false,false,false,false,false,true])) [false,false] false n
    _ = (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,false,false,false,false,false,false,false,true])) [false,false] false n

theorem finalR (n : Nat) : ([false,true,false,true,true,true,true,true]) = ([false,true,false,true,true,true,true,true]) := by
  rfl

theorem epoch (n : Nat) : run0 table (19+3*n) ⟨5,[],(rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])⟩ = some ⟨1,(rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,false,false,true]),([false,true,false,true,true,true,true,true])⟩ := by
  have H := (join0 (join0 (phase0 n) (phase1 n)) (phase2 n))
  rw [finalL n] at H
  rw [show 3+3*n+16=19+3*n by omega] at H
  exact H

theorem canon (n : Nat) : run0 table (19+3*n) ⟨5,[],(rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])⟩ = some ⟨1,(rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,false,false,true]),([false,true,false,true,true,true,true,true])⟩ := by
  exact epoch n

end MInit


namespace MFinish

-- 1RB0RC_1RC1LF_0RD1LF_1LD0RA_0LB---_1LE0LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

theorem local0 (L R : List Bool) : run0 table 3 ⟨1,([true,false,false]) ++ (L),(R)⟩ = some ⟨1,(L),([false,true,true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (3*n) ⟨1,(rep [true,false,false] (n)) ++ ([true,false,false,true,false,false,true,false,false,true]),([false,true,false,true,true,true,true,true])⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false,true]),(rep [false,true,true] (n)) ++ ([false,true,false,true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [] [] [true,false,false] [false,true,true] 3 local0 n (([true,false,false,true,false,false,true,false,false,true])) (([false,true,false,true,true,true,true,true]))

theorem phase1 (n : Nat) : run0 table 10 ⟨1,([true,false,false,true,false,false,true,false,false,true]),(rep [false,true,true] (n)) ++ ([false,true,false,true,true,true,true,true])⟩ = some ⟨5,[],([true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,false,true,true,true,true,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,false,true,true,true,true,true]) = (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,true]) := by
  calc
    _ = ([true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,false,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,true,false,true,true,false,true])) (([false,true,false,true,true,true,true,true])) [false,true] true n
    _ = ([true,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true,true,false,true,false,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,true,false,true,true,false])) (([true,false,true,false,true,true,true,true,true])) [true,false] true n
    _ = ([true,false,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,false,true,false,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,true,false,true,true])) (([true,true,false,true,false,true,true,true,true,true])) [true,true] false n
    _ = ([true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,false,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,true,false,true])) (([false,true,true,false,true,false,true,true,true,true,true])) [false,true] true n
    _ = ([true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true,true,false,true,true,false,true,false,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,true,false])) (([true,false,true,true,false,true,false,true,true,true,true,true])) [true,false] true n
    _ = ([true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,false,true,true,false,true,false,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,true])) (([true,true,false,true,true,false,true,false,true,true,true,true,true])) [true,true] false n
    _ = ([true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,true,false,true,false,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true])) (([false,true,true,false,true,true,false,true,false,true,true,true,true,true])) [false,true] true n
    _ = ([true,false]) ++ (rep [true,true,false] (n)) ++ ([true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false])) (([true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])) [true,false] true n
    _ = ([true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true])) (([true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])) [true,true] false n
    _ = (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])) [false,true] true n

theorem epoch (n : Nat) : run0 table (10+3*n) ⟨1,(rep [true,false,false] (n)) ++ ([true,false,false,true,false,false,true,false,false,true]),([false,true,false,true,true,true,true,true])⟩ = some ⟨5,[],(rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])⟩ := by
  have H := (join0 (phase0 n) (phase1 n))
  rw [finalR n] at H
  rw [show 3*n+10=10+3*n by omega] at H
  exact H

theorem eq1r (n : Nat) : (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,true]) = ([true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,true,false,true,false,true,true,true,true,true]) := by
  calc
    _ = ([true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])) [false,true] true n
    _ = ([true,false]) ++ (rep [true,true,false] (n)) ++ ([true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true])) (([true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])) [true,true] false n
    _ = ([true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,true,false,true,false,true,true,true,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false])) (([true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])) [true,false] true n

theorem canon (n : Nat) : run0 table (10+3*n) ⟨1,(rep [true,false,false] (n)) ++ ([true,false,false,true,false,false,true,false,false,true]),([false,true,false,true,true,true,true,true])⟩ = some ⟨5,[],([true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])⟩ := by
  simpa only [eq1r n] using epoch n

end MFinish


namespace MCarry

-- 1RB0RC_1RC1LF_0RD1LF_1LD0RA_0LB---_1LE0LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

theorem local0 (L R : List Bool) : run0 table 3 ⟨1,([true,false,false]) ++ (L),(R)⟩ = some ⟨1,(L),([false,true,true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) (R : List Bool) : run0 table (3*n) ⟨1,(rep [true,false,false] (n)) ++ ([true,false,false,false,false,false]) ++ (R),([false,true,false,true,true,true,true,true])⟩ = some ⟨1,([true,false,false,false,false,false]) ++ (R),(rep [false,true,true] (n)) ++ ([false,true,false,true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [] [] [true,false,false] [false,true,true] 3 local0 n (([true,false,false,false,false,false]) ++ (R)) (([false,true,false,true,true,true,true,true]))

theorem phase1 (n : Nat) (R : List Bool) : run0 table 4 ⟨1,([true,false,false,false,false,false]) ++ (R),(rep [false,true,true] (n)) ++ ([false,true,false,true,true,true,true,true])⟩ = some ⟨2,([false,true,false,false]) ++ (R),([true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,false,true,true,true,true,true])⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 3 ⟨2,([false]) ++ (L),([true,true]) ++ ([false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([false,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) (R : List Bool) : run0 table (3*n) ⟨2,([false,true,false,false]) ++ (R),([true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,false,true,true,true,true,true])⟩ = some ⟨2,([false]) ++ (rep [false,false,false] (n)) ++ ([true,false,false]) ++ (R),([true,true,false,true,false,true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true] [false,true,true] [false,false,false] 3 local2 n (([true,false,false]) ++ (R)) (([false,true,false,true,true,true,true,true]))

theorem phase3 (n : Nat) (R : List Bool) : run0 table 10 ⟨2,([false]) ++ (rep [false,false,false] (n)) ++ ([true,false,false]) ++ (R),([true,true,false,true,false,true,true,true,true,true])⟩ = some ⟨1,([false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,false,false]) ++ (R),([false,true,false,true,true,true,true,true])⟩ := by rfl

theorem finalL (n : Nat) (R : List Bool) : ([false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,false,false]) ++ (R) = (rep [false,false,false] (n)) ++ ([false,false,false,true,false,false]) ++ (R) := by
  calc
    _ = ([false,false]) ++ (rep [false,false,false] (n)) ++ ([false,true,false,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([true,false,false]) ++ (R)) [false,false] false n
    _ = ([false]) ++ (rep [false,false,false] (n)) ++ ([false,false,true,false,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,true,false,false]) ++ (R)) [false,false] false n
    _ = (rep [false,false,false] (n)) ++ ([false,false,false,true,false,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,false,true,false,false]) ++ (R)) [false,false] false n

theorem finalR (n : Nat) (R : List Bool) : ([false,true,false,true,true,true,true,true]) = ([false,true,false,true,true,true,true,true]) := by
  rfl

theorem epoch (n : Nat) (R : List Bool) : run0 table (14+6*n) ⟨1,(rep [true,false,false] (n)) ++ ([true,false,false,false,false,false]) ++ (R),([false,true,false,true,true,true,true,true])⟩ = some ⟨1,(rep [false,false,false] (n)) ++ ([false,false,false,true,false,false]) ++ (R),([false,true,false,true,true,true,true,true])⟩ := by
  have H := (join0 (join0 (join0 (phase0 n R) (phase1 n R)) (phase2 n R)) (phase3 n R))
  rw [finalL n R] at H
  rw [show 3*n+4+3*n+10=14+6*n by omega] at H
  exact H

theorem canon (n : Nat) (R : List Bool) : run0 table (14+6*n) ⟨1,(rep [true,false,false] (n)) ++ ([true,false,false,false,false,false]) ++ (R),([false,true,false,true,true,true,true,true])⟩ = some ⟨1,(rep [false,false,false] (n)) ++ ([false,false,false,true,false,false]) ++ (R),([false,true,false,true,true,true,true,true])⟩ := by
  exact epoch n R

end MCarry


abbrev table := MInit.table
abbrev A : List Bool := [true,false,false]
abbrev Z : List Bool := [false,false,false]
def Q (R : List Bool) : Z0 := ⟨1,(R),[false,true,false,true,true,true,true,true]⟩
def family (n : Nat) : Z0 := ⟨5,[],(rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,true,false,true,false,true,true,true,true,true])⟩
def carryCost (n : Nat) : Nat := 8+6*n

theorem carry (n : Nat) (R : List Bool) : run0 table (carryCost n) (Q (rep A n ++ Z ++ R)) = some (Q (rep Z n ++ A ++ R)) := by
  cases n with
  | zero => rfl
  | succ n =>
    have h := MCarry.canon n R
    rw [show MCarry.table = table from rfl] at h
    unfold carryCost
    rw [show 8+6*n.succ = 14+6*n by omega]
    rw [rep_succ_snoc A n,rep_succ_snoc Z n]
    simpa only [table,Q,A,Z,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem entry : run0 table 116 ⟨0,[],[]⟩ = some (family 0) := by rfl


def cost (n : Nat) : Nat := (19+3*n) + fillCost carryCost (n+3) + (10+3*n)

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := MInit.canon n
  have h2 := fill table Q A Z carryCost carry (n+3) [true]
  have h3 := MFinish.canon n
  rw [rep_add Z n 3,rep_add A n 3] at h2
  simp only [Q,A,Z,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] at h2
  have h := join0 (join0 h1 h2) h3
  simpa only [cost,family,rep,rep_succ_snoc,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 116 cost entry (by intro n; unfold cost; omega) growth m hm

#print axioms growth
#print axioms never
end M1399

end BB6.Agent11Raw39RCCounter1089
