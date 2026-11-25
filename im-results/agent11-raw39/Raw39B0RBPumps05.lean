import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B0RBPumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M257

-- 1RB0RB_1RC0LF_0RD0LE_1LD0RA_0LB0LA_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨1,([true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨1,([true,false,false,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨1,([true,false,false,true]) ++ (L),([false,true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨1,([true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨1,([true,false,false,true]),(rep [false,true,false,false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false,true] [] [false,false,true,false,false,true] [false,true,false,false,true,false] 6 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 7 ⟨1,([true,false,false,true]),(rep [false,true,false,false,true,false] (n))⟩ = some ⟨2,([false,true]),([true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 34 ⟨2,([false]) ++ (L),([true,false,false,true,false]) ++ ([false,true,false,false,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (34*n) ⟨2,([false,true]),([true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true,false] [false,true,false,false,true,false] [true,false,false,true,false,false] 34 local3 n (([true])) ([])

theorem phase4 (n : Nat) : run0 table 20 ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false])) ([]) [false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (33+40*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 6+6*n+7+34*n+20=33+40*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 33+40*n) entry (by intro n; omega) growth m hm

#print axioms never

end M257

namespace M258

-- 1RB0RB_1RC0LF_0RD0LF_1LD0RA_0LB---_1LE0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨1,([true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨1,([true,false,false,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨1,([true,false,false,true]) ++ (L),([false,true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨1,([true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨1,([true,false,false,true]),(rep [false,true,false,false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false,true] [] [false,false,true,false,false,true] [false,true,false,false,true,false] 6 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 7 ⟨1,([true,false,false,true]),(rep [false,true,false,false,true,false] (n))⟩ = some ⟨2,([false,true]),([true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 34 ⟨2,([false]) ++ (L),([true,false,false,true,false]) ++ ([false,true,false,false,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (34*n) ⟨2,([false,true]),([true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true,false] [false,true,false,false,true,false] [true,false,false,true,false,false] 34 local3 n (([true])) ([])

theorem phase4 (n : Nat) : run0 table 20 ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false])) ([]) [false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (33+40*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 6+6*n+7+34*n+20=33+40*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 33+40*n) entry (by intro n; omega) growth m hm

#print axioms never

end M258

namespace M259

-- 1RB0RB_1RC0LF_0RD0RA_1LD0RA_0LB0LB_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩

theorem entry : run0 table 11 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 5 ⟨5,[],([false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ = some ⟨0,([false,false,false,true]),([false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨0,([false]) ++ (L),([false,true,false]) ++ ([false,true,false,false,true,false]) ++ (R)⟩ = some ⟨0,([false]) ++ ([false,true,true,false,true,true]) ++ (L),([false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨0,([false,false,false,true]),([false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ = some ⟨0,([false]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,false,true]),([false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [false] [false,true,false] [false,true,false,false,true,false] [false,true,true,false,true,true] 6 local1 n (([false,false,true])) ([])

theorem phase2 (n : Nat) : run0 table 13 ⟨0,([false]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,false,true]),([false,true,false])⟩ = some ⟨1,([true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,false,true]),([false,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨1,([true,false,true,true]) ++ ([false,true,true,false,true,true]) ++ (L),(R)⟩ = some ⟨1,([true,false,true,true]) ++ (L),([false,true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨1,([true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,false,true]),([false,true,false])⟩ = some ⟨1,([true,false,true,true,false,false,true]),(rep [false,true,false,false,true,false] (n)) ++ ([false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,true,true] [] [false,true,true,false,true,true] [false,true,false,false,true,false] 6 local3 n (([false,false,true])) (([false,true,false]))

theorem phase4 (n : Nat) : run0 table 7 ⟨1,([true,false,true,true,false,false,true]),(rep [false,true,false,false,true,false] (n)) ++ ([false,true,false])⟩ = some ⟨5,[],([false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([false,true,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([false,true,false]) = ([false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) := by
  calc
    _ = ([false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,false,false,true,false])) (([true,false])) [true,false,false,true,false] false n
    _ = ([false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,false,false,true,false,false])) (([false])) [false,false,true,false,false] true n
    _ = ([false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,false,false,true,false,false,true])) ([]) [false,true,false,false,true] false n

theorem growth (n : Nat) : run0 table (25+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 5+6*n+13+6*n+7=25+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 11 (fun n => 25+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M259

namespace M260

-- 1RB0RB_1RC0LF_0RD0RE_1LD0RA_0LB---_1LE0RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false,true]) ++ (rep [true] (n)),[]⟩

theorem entry : run0 table 35 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false,true]) ++ (rep [true] (n)),[]⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false,true]) ++ (rep [true] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨1,([true,false,false,true,false,false,true,false,false]) ++ ([true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (L),([false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false,true]) ++ (rep [true] (n)),[]⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false,false,true]) ++ (rep [true] (n)),(rep [false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false,true,false,false,true,false,false] [] [true,false,false] [false,true,false] 3 local1 n (([false,true]) ++ (rep [true] (n))) ([])

theorem phase2 (n : Nat) : run0 table 27 ⟨1,([true,false,false,true,false,false,true,false,false,false,true]) ++ (rep [true] (n)),(rep [false,true,false] (n))⟩ = some ⟨1,([false,false,false,false,true,true]) ++ (rep [true] (n)),([false,true,false,true,false]) ++ (rep [false,true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 15 ⟨1,([false]) ++ (L),([false,true,false,true,false]) ++ ([false,true,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,false,true]) ++ (L),([false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (15*n) ⟨1,([false,false,false,false,true,true]) ++ (rep [true] (n)),([false,true,false,true,false]) ++ (rep [false,true,false] (n))⟩ = some ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([false,false,false,true,true]) ++ (rep [true] (n)),([false,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [false,true,false,true,false] [false,true,false] [false,false,true] 15 local3 n (([false,false,false,true,true]) ++ (rep [true] (n))) ([])

theorem phase4 (n : Nat) : run0 table 19 ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([false,false,false,true,true]) ++ (rep [true] (n)),([false,true,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([false,false,false,true,true]) ++ (rep [true] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([false,false,false,true,true]) ++ (rep [true] (n)) = ([false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false,true,true]) ++ (rep [true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false,false,true,true]) ++ (rep [true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false,true])) (([false,false,true,true]) ++ (rep [true] (n))) [false,true] false n
    _ = ([false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false,true,true]) ++ (rep [true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false,true,false])) (([false,true,true]) ++ (rep [true] (n))) [true,false] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (52+18*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 6+3*n+27+15*n+19=52+18*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 35 (fun n => 52+18*n) entry (by intro n; omega) growth m hm

#print axioms never

end M260

namespace M261

-- 1RB0RB_1RC0LF_0RD0RF_1LD0RA_0LB---_1LE0RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false,true]) ++ (rep [true] (n)),[]⟩

theorem entry : run0 table 27 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false,true]) ++ (rep [true] (n)),[]⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false,true]) ++ (rep [true] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨1,([true,false,false,true,false,false,true,false,false]) ++ ([true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (L),([false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false,true]) ++ (rep [true] (n)),[]⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false,false,true]) ++ (rep [true] (n)),(rep [false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false,true,false,false,true,false,false] [] [true,false,false] [false,true,false] 3 local1 n (([false,true]) ++ (rep [true] (n))) ([])

theorem phase2 (n : Nat) : run0 table 19 ⟨1,([true,false,false,true,false,false,true,false,false,false,true]) ++ (rep [true] (n)),(rep [false,true,false] (n))⟩ = some ⟨1,([false,false,false,false,true,true]) ++ (rep [true] (n)),([false,true,false,true,false]) ++ (rep [false,true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 15 ⟨1,([false]) ++ (L),([false,true,false,true,false]) ++ ([false,true,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,false,true]) ++ (L),([false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (15*n) ⟨1,([false,false,false,false,true,true]) ++ (rep [true] (n)),([false,true,false,true,false]) ++ (rep [false,true,false] (n))⟩ = some ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([false,false,false,true,true]) ++ (rep [true] (n)),([false,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [false,true,false,true,false] [false,true,false] [false,false,true] 15 local3 n (([false,false,false,true,true]) ++ (rep [true] (n))) ([])

theorem phase4 (n : Nat) : run0 table 19 ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([false,false,false,true,true]) ++ (rep [true] (n)),([false,true,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([false,false,false,true,true]) ++ (rep [true] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([false,false,false,true,true]) ++ (rep [true] (n)) = ([false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false,true,true]) ++ (rep [true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false,false,true,true]) ++ (rep [true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false,true])) (([false,false,true,true]) ++ (rep [true] (n))) [false,true] false n
    _ = ([false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false,true,true]) ++ (rep [true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false,true,false])) (([false,true,true]) ++ (rep [true] (n))) [true,false] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (44+18*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 6+3*n+19+15*n+19=44+18*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 27 (fun n => 44+18*n) entry (by intro n; omega) growth m hm

#print axioms never

end M261

namespace M262

-- 1RB0RB_1RC0LF_0RD0RF_1LD0RA_0LB---_1LE0RC

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,false,true] (n)),[]⟩ = some ⟨3,([false,false,true,true]) ++ (rep [false,false,true,false,false,false,true] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 27 ⟨3,([false,false,true,true]) ++ ([false,false,true,false,false,false,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true]) ++ (L),([true,true,true,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (27*n) ⟨3,([false,false,true,true]) ++ (rep [false,false,true,false,false,false,true] (n)),[]⟩ = some ⟨3,([false,false,true,true]),(rep [true,true,true,true,false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true] [] [false,false,true,false,false,false,true] [true,true,true,true,false,true,false] 27 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 32 ⟨3,([false,false,true,true]),(rep [true,true,true,true,false,true,false] (n))⟩ = some ⟨2,([false,true]),([true,false,true,true,true,true]) ++ (rep [true,true,true,true,false,true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 45 ⟨2,([false]) ++ (L),([true,false,true,true,true,true]) ++ ([true,true,true,true,false,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false,false]) ++ (L),([true,false,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (45*n) ⟨2,([false,true]),([true,false,true,true,true,true]) ++ (rep [true,true,true,true,false,true,false] (n))⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false,false] (n)) ++ ([true]),([true,false,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,true,true,true,true] [true,true,true,true,false,true,false] [true,false,false,true,false,false,false] 45 local3 n (([true])) ([])

theorem phase4 (n : Nat) : run0 table 15 ⟨2,([false]) ++ (rep [true,false,false,true,false,false,false] (n)) ++ ([true]),([true,false,true,true,true,true])⟩ = some ⟨1,([false,true,false,false,true,false,false,false]) ++ (rep [true,false,false,true,false,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false,false]) ++ (rep [true,false,false,true,false,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,false,true]) ++ (rep [false,false,true,false,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,false,true]) ++ (rep [false,false,true,false,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false,false])) ([]) [false,false,true,false,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (49+72*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 2+27*n+32+45*n+15=49+72*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 49+72*n) entry (by intro n; omega) growth m hm

#print axioms never

end M262

namespace M263

-- 1RB0RB_1RC0LF_0RD1LA_1LD0RA_0LB0RE_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨false,true,4⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨1,([true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨1,([true,false,false,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨1,([true,false,false,true]) ++ (L),([false,true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨1,([true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨1,([true,false,false,true]),(rep [false,true,false,false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false,true] [] [false,false,true,false,false,true] [false,true,false,false,true,false] 6 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 7 ⟨1,([true,false,false,true]),(rep [false,true,false,false,true,false] (n))⟩ = some ⟨2,([false,true]),([true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 42 ⟨2,([false]) ++ (L),([true,false,false,true,false]) ++ ([false,true,false,false,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (42*n) ⟨2,([false,true]),([true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true,false] [false,true,false,false,true,false] [true,false,false,true,false,false] 42 local3 n (([true])) ([])

theorem phase4 (n : Nat) : run0 table 24 ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false])) ([]) [false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (37+48*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 6+6*n+7+42*n+24=37+48*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 37+48*n) entry (by intro n; omega) growth m hm

#print axioms never

end M263

namespace M264

-- 1RB0RB_1RC0LF_0RD1LB_1LD0RA_0LB---_1LE0RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩

theorem entry : run0 table 45 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨1,([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨1,([true,false,false,true,false,false,true,false,false,true]) ++ ([false,false,true]) ++ (L),(R)⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false,true]) ++ (L),([false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨1,([true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false,true,true]) ++ (rep [false] (n)),(rep [false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false,true,false,false,true,false,false,true] [] [false,false,true] [false,true,false] 3 local1 n (([true]) ++ (rep [false] (n))) ([])

theorem phase2 (n : Nat) : run0 table 21 ⟨1,([true,false,false,true,false,false,true,false,false,true,true]) ++ (rep [false] (n)),(rep [false,true,false] (n))⟩ = some ⟨1,([true,false,false,false,true,false]) ++ (rep [false] (n)),([true,false,false,true,false]) ++ (rep [false,true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 15 ⟨1,([true,false,false,false]) ++ (L),([true,false,false,true,false]) ++ ([false,true,false]) ++ (R)⟩ = some ⟨1,([true,false,false,false]) ++ ([false,false,true]) ++ (L),([true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (15*n) ⟨1,([true,false,false,false,true,false]) ++ (rep [false] (n)),([true,false,false,true,false]) ++ (rep [false,true,false] (n))⟩ = some ⟨1,([true,false,false,false]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)),([true,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true,false,false,false] [true,false,false,true,false] [false,true,false] [false,false,true] 15 local3 n (([true,false]) ++ (rep [false] (n))) ([])

theorem phase4 (n : Nat) : run0 table 37 ⟨1,([true,false,false,false]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)),([true,false,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)) = ([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (64+18*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 6+3*n+21+15*n+37=64+18*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 45 (fun n => 64+18*n) entry (by intro n; omega) growth m hm

#print axioms never

end M264

namespace M265

-- 1RB0RB_1RC0LF_0RD1LB_1LD0RA_0LB---_1LE0RE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,true,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨1,([true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨1,([true,false,false,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨1,([true,false,false,true]) ++ (L),([false,true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨1,([true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨1,([true,false,false,true]),(rep [false,true,false,false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false,true] [] [false,false,true,false,false,true] [false,true,false,false,true,false] 6 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 7 ⟨1,([true,false,false,true]),(rep [false,true,false,false,true,false] (n))⟩ = some ⟨2,([false,true]),([true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 18 ⟨2,([false]) ++ (L),([true,false,false,true,false]) ++ ([false,true,false,false,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (18*n) ⟨2,([false,true]),([true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true,false] [false,true,false,false,true,false] [true,false,false,true,false,false] 18 local3 n (([true])) ([])

theorem phase4 (n : Nat) : run0 table 12 ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false])) ([]) [false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (25+24*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 6+6*n+7+18*n+12=25+24*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 25+24*n) entry (by intro n; omega) growth m hm

#print axioms never

end M265

namespace M267

-- 1RB0RB_1RC0LF_0RD1LD_1LD0RA_0LB0LB_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩

theorem entry : run0 table 82 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨1,[],([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ = some ⟨2,([false,true]),([true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 8 ⟨2,([false]) ++ (L),([true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ ([false,true,false,false,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (8*n) ⟨2,([false,true]),([true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,false,true,false,false,true,false,false,true,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true,false,false,true,false,false,true,false,false,true,false] [false,true,false,false,true,false] [true,false,false,true,false,false] 8 local1 n (([true])) ([])

theorem phase2 (n : Nat) : run0 table 25 ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,false,true,false,false,true,false,false,true,false,false,true,false])⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨1,([true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ ([true,false,false,true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (L),([false,true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨1,([true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]),(rep [false,true,false,false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false] [] [true,false,false,true,false,false] [false,true,false,false,true,false] 6 local3 n (([true])) ([])

theorem phase4 (n : Nat) : run0 table 21 ⟨1,([true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]),(rep [false,true,false,false,true,false] (n))⟩ = some ⟨1,[],([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) = ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (47+14*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 1+8*n+25+6*n+21=47+14*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 82 (fun n => 47+14*n) entry (by intro n; omega) growth m hm

#print axioms never

end M267

end BB6.Agent11Raw39B0RBPumps
