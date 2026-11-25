import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B1RCPumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M1021

-- 1RB1RC_1RC0LE_0RD1LB_1LD0RA_1LF0LA_---1LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,([false,false,true,true]) ++ (rep [false,true,true] (n)),[]⟩

theorem entry : run0 table 3 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 13 ⟨3,([false,false,true,true]) ++ ([false,true,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true]) ++ (L),([true,false,true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (13*n) ⟨3,([false,false,true,true]) ++ (rep [false,true,true] (n)),[]⟩ = some ⟨3,([false,false,true,true]),(rep [true,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true] [] [false,true,true] [true,false,true] 13 local0 n ([]) ([])

theorem phase1 (n : Nat) : run0 table 12 ⟨3,([false,false,true,true]),(rep [true,false,true] (n))⟩ = some ⟨1,([false,true]),([false,true,false,true]) ++ (rep [true,false,true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 7 ⟨1,([false]) ++ (L),([false,true,false,true]) ++ ([true,false,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,false,true]) ++ (L),([false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (7*n) ⟨1,([false,true]),([false,true,false,true]) ++ (rep [true,false,true] (n))⟩ = some ⟨1,([false]) ++ (rep [true,false,true] (n)) ++ ([true]),([false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [false,true,false,true] [true,false,true] [true,false,true] 7 local2 n (([true])) ([])

theorem phase3 (n : Nat) : run0 table 9 ⟨1,([false]) ++ (rep [true,false,true] (n)) ++ ([true]),([false,true,false,true])⟩ = some ⟨3,([false,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true]) = ([false,false,true,true,false,true,true]) ++ (rep [false,true,true] (n)) := by
  calc
    _ = ([false,false,true,true,false,true,true]) ++ (rep [false,true,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,true,false,true])) ([]) [false,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (21+20*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 13*n+12+7*n+9=21+20*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 3 (fun n => 21+20*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1021

namespace M1041

-- 1RB1RC_1RC0LF_0RD1LB_1LD0RA_---1LA_1LE0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨true,false,0⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,([false,false,true,true]) ++ (rep [false,true,true] (n)),[]⟩

theorem entry : run0 table 3 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 13 ⟨3,([false,false,true,true]) ++ ([false,true,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true]) ++ (L),([true,false,true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (13*n) ⟨3,([false,false,true,true]) ++ (rep [false,true,true] (n)),[]⟩ = some ⟨3,([false,false,true,true]),(rep [true,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true] [] [false,true,true] [true,false,true] 13 local0 n ([]) ([])

theorem phase1 (n : Nat) : run0 table 12 ⟨3,([false,false,true,true]),(rep [true,false,true] (n))⟩ = some ⟨1,([false,true]),([false,true,false,true]) ++ (rep [true,false,true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 7 ⟨1,([false]) ++ (L),([false,true,false,true]) ++ ([true,false,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,false,true]) ++ (L),([false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (7*n) ⟨1,([false,true]),([false,true,false,true]) ++ (rep [true,false,true] (n))⟩ = some ⟨1,([false]) ++ (rep [true,false,true] (n)) ++ ([true]),([false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [false,true,false,true] [true,false,true] [true,false,true] 7 local2 n (([true])) ([])

theorem phase3 (n : Nat) : run0 table 9 ⟨1,([false]) ++ (rep [true,false,true] (n)) ++ ([true]),([false,true,false,true])⟩ = some ⟨3,([false,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true]) = ([false,false,true,true,false,true,true]) ++ (rep [false,true,true] (n)) := by
  calc
    _ = ([false,false,true,true,false,true,true]) ++ (rep [false,true,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,true,false,true])) ([]) [false,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (21+20*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 13*n+12+7*n+9=21+20*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 3 (fun n => 21+20*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1041

namespace M1053

-- 1RB1RC_1RC1LE_0RD1LB_1LD0RA_0LF---_0LC0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,2⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true]) ++ (rep [false,false,true] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨2,([false,true]) ++ (rep [false,false,true] (n)) ++ ([true]),[]⟩ = some ⟨3,([false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 9 ⟨3,([false,false,true]) ++ ([false,false,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true]) ++ (L),([false,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (9*n) ⟨3,([false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true]),[]⟩ = some ⟨3,([false,false,true,true]),(rep [false,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true] [] [false,false,true] [false,true,true] 9 local1 n (([true])) ([])

theorem phase2 (n : Nat) : run0 table 10 ⟨3,([false,false,true,true]),(rep [false,true,true] (n))⟩ = some ⟨2,([false,true,true]),([true,true]) ++ (rep [false,true,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨2,([false]) ++ (L),([true,true]) ++ ([false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨2,([false,true,true]),([true,true]) ++ (rep [false,true,true] (n))⟩ = some ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([true,true]),([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true] [false,true,true] [true,false,false] 3 local3 n (([true,true])) ([])

theorem phase4 (n : Nat) : run0 table 3 ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([true,true]),([true,true])⟩ = some ⟨2,([false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([true,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([true,true]) = ([false,true,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true]) := by
  calc
    _ = ([false,true,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false])) (([true])) [false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (14+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 1+9*n+10+3*n+3=14+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 14+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1053

namespace M1057

-- 1RB1RC_1RC1LE_0RD1LB_1LD0RA_1LF---_0LB0LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true])⟩

theorem entry : run0 table 11 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨1,[],([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true])⟩ = some ⟨2,([false,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨2,([false]) ++ (L),([true,true]) ++ ([false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨2,([false,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([true])⟩ = some ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true] [false,true,true] [true,false,false] 3 local1 n (([true])) (([true]))

theorem phase2 (n : Nat) : run0 table 4 ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true])⟩ = some ⟨1,([true,false,false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([true,false,false]) ++ ([true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,false]) ++ (L),([false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([true,false,false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true])⟩ = some ⟨1,([true,false,false,true]),(rep [false,true,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false] [] [true,false,false] [false,true,true] 3 local3 n (([true])) (([true]))

theorem phase4 (n : Nat) : run0 table 6 ⟨1,([true,false,false,true]),(rep [false,true,true] (n)) ++ ([true])⟩ = some ⟨1,[],([false,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true]) = ([false,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true]) := by
  rfl

theorem growth (n : Nat) : run0 table (11+6*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 1+3*n+4+3*n+6=11+6*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 11 (fun n => 11+6*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1057

namespace M1059

-- 1RB1RC_1RC1LE_0RD1LB_1LD0RA_1LF---_0LB0LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true,true])⟩

theorem entry : run0 table 21 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨5,[],([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true,true])⟩ = some ⟨2,([false,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨2,([false]) ++ (L),([true,true]) ++ ([false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨2,([false,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true,true])⟩ = some ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true] [false,true,true] [true,false,false] 3 local1 n (([true])) (([true,true,true,true]))

theorem phase2 (n : Nat) : run0 table 4 ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true,true,true])⟩ = some ⟨1,([true,false,false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([true,false,false]) ++ ([true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,false]) ++ (L),([false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([true,false,false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true])⟩ = some ⟨1,([true,false,false,true]),(rep [false,true,true] (n)) ++ ([true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false] [] [true,false,false] [false,true,true] 3 local3 n (([true])) (([true,true,true,true]))

theorem phase4 (n : Nat) : run0 table 5 ⟨1,([true,false,false,true]),(rep [false,true,true] (n)) ++ ([true,true,true,true])⟩ = some ⟨5,[],([true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true,true]) = ([true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true,true]) := by
  rfl

theorem growth (n : Nat) : run0 table (11+6*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 2+3*n+4+3*n+5=11+6*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 21 (fun n => 11+6*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1059

namespace M1060

-- 1RB1RC_1RC1LE_0RD1LB_1LD0RA_1LF---_0LB0RA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨false,true,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true])⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨5,[],([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true])⟩ = some ⟨2,([false,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨2,([false]) ++ (L),([true,true]) ++ ([false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨2,([false,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true])⟩ = some ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true] [false,true,true] [true,false,false] 3 local1 n (([true])) (([true,true]))

theorem phase2 (n : Nat) : run0 table 4 ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true])⟩ = some ⟨1,([true,false,false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([true,false,false]) ++ ([true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,false]) ++ (L),([false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([true,false,false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true])⟩ = some ⟨1,([true,false,false,true]),(rep [false,true,true] (n)) ++ ([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false] [] [true,false,false] [false,true,true] 3 local3 n (([true])) (([true,true]))

theorem phase4 (n : Nat) : run0 table 5 ⟨1,([true,false,false,true]),(rep [false,true,true] (n)) ++ ([true,true])⟩ = some ⟨5,[],([true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true]) = ([true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true]) := by
  rfl

theorem growth (n : Nat) : run0 table (11+6*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 2+3*n+4+3*n+5=11+6*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 15 (fun n => 11+6*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1060

namespace M1061

-- 1RB1RC_1RC1LE_0RD1LB_1LD0RA_1LF---_0LB0RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true])⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨5,[],([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true])⟩ = some ⟨2,([false,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨2,([false]) ++ (L),([true,true]) ++ ([false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨2,([false,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true])⟩ = some ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true] [false,true,true] [true,false,false] 3 local1 n (([true])) (([true,true]))

theorem phase2 (n : Nat) : run0 table 4 ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true])⟩ = some ⟨1,([true,false,false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([true,false,false]) ++ ([true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,false]) ++ (L),([false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([true,false,false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true])⟩ = some ⟨1,([true,false,false,true]),(rep [false,true,true] (n)) ++ ([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false] [] [true,false,false] [false,true,true] 3 local3 n (([true])) (([true,true]))

theorem phase4 (n : Nat) : run0 table 5 ⟨1,([true,false,false,true]),(rep [false,true,true] (n)) ++ ([true,true])⟩ = some ⟨5,[],([true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true]) = ([true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true]) := by
  rfl

theorem growth (n : Nat) : run0 table (11+6*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 2+3*n+4+3*n+5=11+6*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 11+6*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1061

namespace M1062

-- 1RB1RC_1RC1LE_0RD1LB_1LD0RA_1LF---_0LB0RC

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true])⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 3 ⟨4,[],([true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true])⟩ = some ⟨2,([false,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨2,([false]) ++ (L),([true,true]) ++ ([false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨2,([false,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true])⟩ = some ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true] [false,true,true] [true,false,false] 3 local1 n (([true])) (([true,true,true]))

theorem phase2 (n : Nat) : run0 table 4 ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true,true])⟩ = some ⟨1,([true,false,false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([true,false,false]) ++ ([true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,false]) ++ (L),([false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([true,false,false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true])⟩ = some ⟨1,([true,false,false,true]),(rep [false,true,true] (n)) ++ ([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false] [] [true,false,false] [false,true,true] 3 local3 n (([true])) (([true,true,true]))

theorem phase4 (n : Nat) : run0 table 4 ⟨1,([true,false,false,true]),(rep [false,true,true] (n)) ++ ([true,true,true])⟩ = some ⟨4,[],([true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true]) = ([true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true]) := by
  rfl

theorem growth (n : Nat) : run0 table (11+6*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 3+3*n+4+3*n+4=11+6*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 15 (fun n => 11+6*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1062

namespace M1063

-- 1RB1RC_1RC1LE_0RD1LB_1LD0RA_1LF---_0LB0RD

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨false,true,3⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true])⟩

theorem entry : run0 table 17 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨1,[],([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true])⟩ = some ⟨2,([false,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨2,([false]) ++ (L),([true,true]) ++ ([false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨2,([false,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([true])⟩ = some ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true] [false,true,true] [true,false,false] 3 local1 n (([true])) (([true]))

theorem phase2 (n : Nat) : run0 table 4 ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true])⟩ = some ⟨1,([true,false,false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([true,false,false]) ++ ([true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,false]) ++ (L),([false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([true,false,false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true])⟩ = some ⟨1,([true,false,false,true]),(rep [false,true,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false] [] [true,false,false] [false,true,true] 3 local3 n (([true])) (([true]))

theorem phase4 (n : Nat) : run0 table 6 ⟨1,([true,false,false,true]),(rep [false,true,true] (n)) ++ ([true])⟩ = some ⟨1,[],([false,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true]) = ([false,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true]) := by
  rfl

theorem growth (n : Nat) : run0 table (11+6*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 1+3*n+4+3*n+6=11+6*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 17 (fun n => 11+6*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1063

namespace M1064

-- 1RB1RC_1RC1LE_0RD1LB_1LD0RA_1LF---_0LB0RF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨false,true,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true])⟩

theorem entry : run0 table 35 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨5,[],([true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true])⟩ = some ⟨2,([false,true]),([true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨2,([false]) ++ (L),([true,true,false,true,true]) ++ ([false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false]) ++ (L),([true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨2,([false,true]),([true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true])⟩ = some ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,false,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true,true] [false,true,true] [true,false,false] 3 local1 n (([true])) (([true]))

theorem phase2 (n : Nat) : run0 table 7 ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,false,true,true,true])⟩ = some ⟨1,([true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([true,false,false,true,false,false]) ++ ([true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,false,true,false,false]) ++ (L),([false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true])⟩ = some ⟨1,([true,false,false,true,false,false,true]),(rep [false,true,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false,true,false,false] [] [true,false,false] [false,true,true] 3 local3 n (([true])) (([true]))

theorem phase4 (n : Nat) : run0 table 8 ⟨1,([true,false,false,true,false,false,true]),(rep [false,true,true] (n)) ++ ([true])⟩ = some ⟨5,[],([true,true,false,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,false,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true]) = ([true,true,false,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true]) := by
  rfl

theorem growth (n : Nat) : run0 table (17+6*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 2+3*n+7+3*n+8=17+6*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 35 (fun n => 17+6*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1064

end BB6.Agent11Raw39B1RCPumps
