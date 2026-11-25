import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39RCPumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M359

-- 1RB0RC_1RC1LF_0RD0RE_1LD0RA_1LE1LB_---1LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,4⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([true,true,true,true,true]) ++ (rep [true,true] (n))⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨1,[],([true,true,true,true,true]) ++ (rep [true,true] (n))⟩ = some ⟨2,([true,true]),([true,true,true,true]) ++ (rep [true,true] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨2,([true]) ++ (L),([true,true,true,true]) ++ ([true,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true]) ++ (L),([true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨2,([true,true]),([true,true,true,true]) ++ (rep [true,true] (n))⟩ = some ⟨2,([true]) ++ (rep [true,true] (n)) ++ ([true]),([true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true,true,true,true] [true,true] [true,true] 6 local1 n (([true])) ([])

theorem phase2 (n : Nat) : run0 table 16 ⟨2,([true]) ++ (rep [true,true] (n)) ++ ([true]),([true,true,true,true])⟩ = some ⟨1,([true,true,true]) ++ (rep [true,true] (n)) ++ ([true]),([true,true,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 2 ⟨1,([true,true,true]) ++ ([true,true]) ++ (L),(R)⟩ = some ⟨1,([true,true,true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (2*n) ⟨1,([true,true,true]) ++ (rep [true,true] (n)) ++ ([true]),([true,true,true])⟩ = some ⟨1,([true,true,true,true]),(rep [true,true] (n)) ++ ([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,true] [] [true,true] [true,true] 2 local3 n (([true])) (([true,true,true]))

theorem phase4 (n : Nat) : run0 table 4 ⟨1,([true,true,true,true]),(rep [true,true] (n)) ++ ([true,true,true])⟩ = some ⟨1,[],([true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,true,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,true,true]) = ([true,true,true,true,true,true,true]) ++ (rep [true,true] (n)) := by
  calc
    _ = ([true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true,true,true])) (([true,true])) [true] true n
    _ = ([true,true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true,true,true,true])) (([true])) [true] true n
    _ = ([true,true,true,true,true,true,true]) ++ (rep [true,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true,true,true,true,true])) ([]) [true] true n

theorem growth (n : Nat) : run0 table (21+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 1+6*n+16+2*n+4=21+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 21+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M359

namespace M489

-- 1RB0RC_1RC0RD_0RD0RF_1LD0RA_1LF---_0LE0LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 2 ⟨5,([false,false,false,false]) ++ ([false,false]) ++ (L),(R)⟩ = some ⟨5,([false,false,false,false]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (2*n) ⟨5,([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]),[]⟩ = some ⟨5,([false,false,false,false,true]),(rep [true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,false,false] [] [false,false] [true,false] 2 local0 n (([true])) ([])

theorem phase1 (n : Nat) : run0 table 10 ⟨5,([false,false,false,false,true]),(rep [true,false] (n))⟩ = some ⟨3,([false,false,true,false,false,true]),(rep [true,false] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 8 ⟨3,([false,false,true]) ++ (L),([true,false]) ++ (R)⟩ = some ⟨3,([false,false,true]) ++ ([false,false]) ++ (L),(R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (8*n) ⟨3,([false,false,true,false,false,true]),(rep [true,false] (n))⟩ = some ⟨3,([false,false,true]) ++ (rep [false,false] (n)) ++ ([false,false,true]),[]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [false,false,true] [] [true,false] [false,false] 8 local2 n (([false,false,true])) ([])

theorem phase3 (n : Nat) : run0 table 5 ⟨3,([false,false,true]) ++ (rep [false,false] (n)) ++ ([false,false,true]),[]⟩ = some ⟨5,([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false,false,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false,false,true]) = ([false,false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]) := by
  calc
    _ = ([false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false])) (([false,true])) [false] false n
    _ = ([false,false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false])) (([true])) [false] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (15+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 2*n+10+8*n+5=15+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (fun n => 15+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M489

namespace M490

-- 1RB0RC_1RC1LC_0RD0RF_1LD0RA_1LF---_0LE0LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 2 ⟨5,([false,false,false,false]) ++ ([false,false]) ++ (L),(R)⟩ = some ⟨5,([false,false,false,false]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (2*n) ⟨5,([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]),[]⟩ = some ⟨5,([false,false,false,false,true]),(rep [true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,false,false] [] [false,false] [true,false] 2 local0 n (([true])) ([])

theorem phase1 (n : Nat) : run0 table 10 ⟨5,([false,false,false,false,true]),(rep [true,false] (n))⟩ = some ⟨2,([true,false,false,true]),([true,false]) ++ (rep [true,false] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 8 ⟨2,([true]) ++ (L),([true,false]) ++ ([true,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([false,false]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (8*n) ⟨2,([true,false,false,true]),([true,false]) ++ (rep [true,false] (n))⟩ = some ⟨2,([true]) ++ (rep [false,false] (n)) ++ ([false,false,true]),([true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true,false] [true,false] [false,false] 8 local2 n (([false,false,true])) ([])

theorem phase3 (n : Nat) : run0 table 9 ⟨2,([true]) ++ (rep [false,false] (n)) ++ ([false,false,true]),([true,false])⟩ = some ⟨5,([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false,false,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false,false,true]) = ([false,false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]) := by
  calc
    _ = ([false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false])) (([false,true])) [false] false n
    _ = ([false,false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false])) (([true])) [false] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (19+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 2*n+10+8*n+9=19+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (fun n => 19+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M490

namespace M491

-- 1RB0RC_1RC0RD_0RD0RF_1LD0RA_1LF---_0LE1LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 2 ⟨5,([false,false,false,false]) ++ ([false,false]) ++ (L),(R)⟩ = some ⟨5,([false,false,false,false]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (2*n) ⟨5,([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]),[]⟩ = some ⟨5,([false,false,false,false,true]),(rep [true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,false,false] [] [false,false] [true,false] 2 local0 n (([true])) ([])

theorem phase1 (n : Nat) : run0 table 8 ⟨5,([false,false,false,false,true]),(rep [true,false] (n))⟩ = some ⟨0,([false,false,false,true]),([true,false]) ++ (rep [true,false] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 8 ⟨0,([false]) ++ (L),([true,false]) ++ ([true,false]) ++ (R)⟩ = some ⟨0,([false]) ++ ([false,false]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (8*n) ⟨0,([false,false,false,true]),([true,false]) ++ (rep [true,false] (n))⟩ = some ⟨0,([false]) ++ (rep [false,false] (n)) ++ ([false,false,true]),([true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [false] [true,false] [true,false] [false,false] 8 local2 n (([false,false,true])) ([])

theorem phase3 (n : Nat) : run0 table 7 ⟨0,([false]) ++ (rep [false,false] (n)) ++ ([false,false,true]),([true,false])⟩ = some ⟨5,([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false,false,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false,false,true]) = ([false,false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]) := by
  calc
    _ = ([false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false])) (([false,true])) [false] false n
    _ = ([false,false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false])) (([true])) [false] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (15+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 2*n+8+8*n+7=15+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (fun n => 15+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M491

namespace M632

-- 1RB0RC_1RC0LE_0RD0RF_1LD0RA_---1RF_1LF1LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([true,true,true,true,true]) ++ (rep [true,true] (n))⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨1,[],([true,true,true,true,true]) ++ (rep [true,true] (n))⟩ = some ⟨2,([true,true]),([true,true,true,true]) ++ (rep [true,true] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨2,([true]) ++ (L),([true,true,true,true]) ++ ([true,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true]) ++ (L),([true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨2,([true,true]),([true,true,true,true]) ++ (rep [true,true] (n))⟩ = some ⟨2,([true]) ++ (rep [true,true] (n)) ++ ([true]),([true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true,true,true,true] [true,true] [true,true] 6 local1 n (([true])) ([])

theorem phase2 (n : Nat) : run0 table 14 ⟨2,([true]) ++ (rep [true,true] (n)) ++ ([true]),([true,true,true,true])⟩ = some ⟨5,([false,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true]),([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 4 ⟨5,([false,true,true,true,true]) ++ ([true,true]) ++ (L),(R)⟩ = some ⟨5,([false,true,true,true,true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (4*n) ⟨5,([false,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true]),([true])⟩ = some ⟨5,([false,true,true,true,true,true]),(rep [true,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true,true,true,true] [] [true,true] [true,true] 4 local3 n (([true])) (([true]))

theorem phase4 (n : Nat) : run0 table 10 ⟨5,([false,true,true,true,true,true]),(rep [true,true] (n)) ++ ([true])⟩ = some ⟨1,[],([true,true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true]) = ([true,true,true,true,true,true,true]) ++ (rep [true,true] (n)) := by
  calc
    _ = ([true,true,true,true,true,true,true]) ++ (rep [true,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true,true,true,true,true])) ([]) [true] true n

theorem growth (n : Nat) : run0 table (25+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 1+6*n+14+4*n+10=25+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 25+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M632

namespace M637

-- 1RB0RC_1RC1LE_0RD0RF_1LD0RA_---1LB_1LF1LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([true,true,true,true,true]) ++ (rep [true,true] (n))⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨1,[],([true,true,true,true,true]) ++ (rep [true,true] (n))⟩ = some ⟨2,([true,true]),([true,true,true,true]) ++ (rep [true,true] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨2,([true]) ++ (L),([true,true,true,true]) ++ ([true,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true]) ++ (L),([true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨2,([true,true]),([true,true,true,true]) ++ (rep [true,true] (n))⟩ = some ⟨2,([true]) ++ (rep [true,true] (n)) ++ ([true]),([true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true,true,true,true] [true,true] [true,true] 6 local1 n (([true])) ([])

theorem phase2 (n : Nat) : run0 table 16 ⟨2,([true]) ++ (rep [true,true] (n)) ++ ([true]),([true,true,true,true])⟩ = some ⟨1,([true,true,true]) ++ (rep [true,true] (n)) ++ ([true]),([true,true,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 2 ⟨1,([true,true,true]) ++ ([true,true]) ++ (L),(R)⟩ = some ⟨1,([true,true,true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (2*n) ⟨1,([true,true,true]) ++ (rep [true,true] (n)) ++ ([true]),([true,true,true])⟩ = some ⟨1,([true,true,true,true]),(rep [true,true] (n)) ++ ([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,true] [] [true,true] [true,true] 2 local3 n (([true])) (([true,true,true]))

theorem phase4 (n : Nat) : run0 table 4 ⟨1,([true,true,true,true]),(rep [true,true] (n)) ++ ([true,true,true])⟩ = some ⟨1,[],([true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,true,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,true,true]) = ([true,true,true,true,true,true,true]) ++ (rep [true,true] (n)) := by
  calc
    _ = ([true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true,true,true])) (([true,true])) [true] true n
    _ = ([true,true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true,true,true,true])) (([true])) [true] true n
    _ = ([true,true,true,true,true,true,true]) ++ (rep [true,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true,true,true,true,true])) ([]) [true] true n

theorem growth (n : Nat) : run0 table (21+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 1+6*n+16+2*n+4=21+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 21+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M637

namespace M690

-- 1RB0RC_1RC0LE_0RD1LA_1LD0RA_0LB0LF_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false])⟩

theorem entry : run0 table 14 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨4,[],([true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false])⟩ = some ⟨2,([false,true]),([true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 8 ⟨2,([false]) ++ (L),([true,false]) ++ ([false,false,true,false,false,false,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (8*n) ⟨2,([false,true]),([true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false] [false,false,true,false,false,false,true,false] [true,true,false,false,true,true,false,false] 8 local1 n (([true])) (([true,false,false]))

theorem phase2 (n : Nat) : run0 table 3 ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,true,false,false])⟩ = some ⟨1,([true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([false,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 8 ⟨1,([true,true,false,false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,false]) ++ (L),([false,true,false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (8*n) ⟨1,([true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([false,false])⟩ = some ⟨1,([true,true,false,false,true]),(rep [false,true,false,false,false,true,false,false] (n)) ++ ([false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,false] [] [true,true,false,false,true,true,false,false] [false,true,false,false,false,true,false,false] 8 local3 n (([true])) (([false,false]))

theorem phase4 (n : Nat) : run0 table 19 ⟨1,([true,true,false,false,true]),(rep [false,true,false,false,false,true,false,false] (n)) ++ ([false,false])⟩ = some ⟨2,([false,true]),([true,false,false,false,true,false,false]) ++ (rep [false,true,false,false,false,true,false,false] (n)) ++ ([false,false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 8 ⟨2,([false]) ++ (L),([true,false,false,false,true,false,false]) ++ ([false,true,false,false,false,true,false,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),([true,false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (8*n) ⟨2,([false,true]),([true,false,false,false,true,false,false]) ++ (rep [false,true,false,false,false,true,false,false] (n)) ++ ([false,false])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,false,true,false,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,false,true,false,false] [false,true,false,false,false,true,false,false] [true,true,false,false,true,true,false,false] 8 local5 n (([true])) (([false,false]))

theorem phase6 (n : Nat) : run0 table 18 ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,false,true,false,false,false,false])⟩ = some ⟨4,([true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 8 ⟨4,([true,false,false,true,true,false,false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),(R)⟩ = some ⟨4,([true,false,false,true,true,false,false]) ++ (L),([false,false,true,false,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (8*n) ⟨4,([true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false])⟩ = some ⟨4,([true,false,false,true,true,false,false,true]),(rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,false,true,true,false,false] [] [true,true,false,false,true,true,false,false] [false,false,true,false,false,false,true,false] 8 local7 n (([true])) (([true,false,false]))

theorem phase8 (n : Nat) : run0 table 20 ⟨4,([true,false,false,true,true,false,false,true]),(rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false])⟩ = some ⟨4,[],([true,false,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false]) = ([true,false,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false]) := by
  rfl

theorem growth (n : Nat) : run0 table (62+32*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 2+8*n+3+8*n+19+8*n+18+8*n+20=62+32*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 14 (fun n => 62+32*n) entry (by intro n; omega) growth m hm

#print axioms never

end M690

namespace M691

-- 1RB0RC_1RC0LF_0RD1LA_1LD0RA_1LF---_0LB0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false])⟩

theorem entry : run0 table 14 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨5,[],([true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false])⟩ = some ⟨2,([false,true]),([true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 8 ⟨2,([false]) ++ (L),([true,false]) ++ ([false,false,true,false,false,false,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (8*n) ⟨2,([false,true]),([true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false] [false,false,true,false,false,false,true,false] [true,true,false,false,true,true,false,false] 8 local1 n (([true])) (([true,false,false]))

theorem phase2 (n : Nat) : run0 table 3 ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,true,false,false])⟩ = some ⟨1,([true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([false,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 8 ⟨1,([true,true,false,false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,false]) ++ (L),([false,true,false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (8*n) ⟨1,([true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([false,false])⟩ = some ⟨1,([true,true,false,false,true]),(rep [false,true,false,false,false,true,false,false] (n)) ++ ([false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,false] [] [true,true,false,false,true,true,false,false] [false,true,false,false,false,true,false,false] 8 local3 n (([true])) (([false,false]))

theorem phase4 (n : Nat) : run0 table 19 ⟨1,([true,true,false,false,true]),(rep [false,true,false,false,false,true,false,false] (n)) ++ ([false,false])⟩ = some ⟨2,([false,true]),([true,false,false,false,true,false,false]) ++ (rep [false,true,false,false,false,true,false,false] (n)) ++ ([false,false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 8 ⟨2,([false]) ++ (L),([true,false,false,false,true,false,false]) ++ ([false,true,false,false,false,true,false,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),([true,false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (8*n) ⟨2,([false,true]),([true,false,false,false,true,false,false]) ++ (rep [false,true,false,false,false,true,false,false] (n)) ++ ([false,false])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,false,true,false,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,false,true,false,false] [false,true,false,false,false,true,false,false] [true,true,false,false,true,true,false,false] 8 local5 n (([true])) (([false,false]))

theorem phase6 (n : Nat) : run0 table 18 ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,false,true,false,false,false,false])⟩ = some ⟨5,([true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 8 ⟨5,([true,false,false,true,true,false,false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),(R)⟩ = some ⟨5,([true,false,false,true,true,false,false]) ++ (L),([false,false,true,false,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (8*n) ⟨5,([true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false])⟩ = some ⟨5,([true,false,false,true,true,false,false,true]),(rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,false,false,true,true,false,false] [] [true,true,false,false,true,true,false,false] [false,false,true,false,false,false,true,false] 8 local7 n (([true])) (([true,false,false]))

theorem phase8 (n : Nat) : run0 table 20 ⟨5,([true,false,false,true,true,false,false,true]),(rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false])⟩ = some ⟨5,[],([true,false,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false]) = ([true,false,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false]) := by
  rfl

theorem growth (n : Nat) : run0 table (62+32*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 2+8*n+3+8*n+19+8*n+18+8*n+20=62+32*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 14 (fun n => 62+32*n) entry (by intro n; omega) growth m hm

#print axioms never

end M691

namespace M693

-- 1RB0RC_1RC0RE_0RD1LA_1LD0RA_0LD0RF_---0RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,3⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true]) ++ (rep [false,false,false] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩

theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 13 ⟨2,([false,true]) ++ (rep [false,false,false] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ = some ⟨3,([false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨3,([false,false,false,false,false]) ++ ([false,false,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,false,false]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨3,([false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ = some ⟨3,([false,false,false,false,false,true]) ++ (rep [false,false] (n)),(rep [true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,false,false] [] [false,false,false] [true,true,true] 3 local1 n (([true]) ++ (rep [false,false] (n))) ([])

theorem phase2 (n : Nat) : run0 table 9 ⟨3,([false,false,false,false,false,true]) ++ (rep [false,false] (n)),(rep [true,true,true] (n))⟩ = some ⟨1,([true,true,false]) ++ (rep [false,false] (n)),([true,true,true]) ++ (rep [true,true,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([true]) ++ (L),([true,true,true]) ++ ([true,true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([false,false,false]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([true,true,false]) ++ (rep [false,false] (n)),([true,true,true]) ++ (rep [true,true,true] (n))⟩ = some ⟨1,([true]) ++ (rep [false,false,false] (n)) ++ ([true,false]) ++ (rep [false,false] (n)),([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,true,true] [true,true,true] [false,false,false] 3 local3 n (([true,false]) ++ (rep [false,false] (n))) ([])

theorem phase4 (n : Nat) : run0 table 5 ⟨1,([true]) ++ (rep [false,false,false] (n)) ++ ([true,false]) ++ (rep [false,false] (n)),([true,true,true])⟩ = some ⟨3,([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,false]) ++ (rep [false,false] (n)),([false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 3 ⟨3,([false,false,false,false]) ++ ([false,false,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,false]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (3*n) ⟨3,([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,false]) ++ (rep [false,false] (n)),([false])⟩ = some ⟨3,([false,false,false,false,true,false]) ++ (rep [false,false] (n)),(rep [true,true,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,false] [] [false,false,false] [true,true,true] 3 local5 n (([true,false]) ++ (rep [false,false] (n))) (([false]))

theorem phase6 (n : Nat) : run0 table 8 ⟨3,([false,false,false,false,true,false]) ++ (rep [false,false] (n)),(rep [true,true,true] (n)) ++ ([false])⟩ = some ⟨1,([true,true,false,false]) ++ (rep [false,false] (n)),([true,true]) ++ (rep [true,true,true] (n)) ++ ([false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 3 ⟨1,([true]) ++ (L),([true,true]) ++ ([true,true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([false,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (3*n) ⟨1,([true,true,false,false]) ++ (rep [false,false] (n)),([true,true]) ++ (rep [true,true,true] (n)) ++ ([false])⟩ = some ⟨1,([true]) ++ (rep [false,false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),([true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,true] [true,true,true] [false,false,false] 3 local7 n (([true,false,false]) ++ (rep [false,false] (n))) (([false]))

theorem phase8 (n : Nat) : run0 table 4 ⟨1,([true]) ++ (rep [false,false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),([true,true,false])⟩ = some ⟨2,([false,true,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)) = ([false,true,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (39+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 13+3*n+9+3*n+5+3*n+8+3*n+4=39+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 39+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M693

namespace M722

-- 1RB0RC_1RC0RF_0RD1LA_1LD0RA_---0RB_0LD0RE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,false => some (some ⟨false,false,3⟩)
  | 5,true => some (some ⟨false,true,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true]) ++ (rep [false,false,false] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩

theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 13 ⟨2,([false,true]) ++ (rep [false,false,false] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ = some ⟨3,([false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨3,([false,false,false,false,false]) ++ ([false,false,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,false,false]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨3,([false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ = some ⟨3,([false,false,false,false,false,true]) ++ (rep [false,false] (n)),(rep [true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,false,false] [] [false,false,false] [true,true,true] 3 local1 n (([true]) ++ (rep [false,false] (n))) ([])

theorem phase2 (n : Nat) : run0 table 9 ⟨3,([false,false,false,false,false,true]) ++ (rep [false,false] (n)),(rep [true,true,true] (n))⟩ = some ⟨1,([true,true,false]) ++ (rep [false,false] (n)),([true,true,true]) ++ (rep [true,true,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([true]) ++ (L),([true,true,true]) ++ ([true,true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([false,false,false]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([true,true,false]) ++ (rep [false,false] (n)),([true,true,true]) ++ (rep [true,true,true] (n))⟩ = some ⟨1,([true]) ++ (rep [false,false,false] (n)) ++ ([true,false]) ++ (rep [false,false] (n)),([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,true,true] [true,true,true] [false,false,false] 3 local3 n (([true,false]) ++ (rep [false,false] (n))) ([])

theorem phase4 (n : Nat) : run0 table 5 ⟨1,([true]) ++ (rep [false,false,false] (n)) ++ ([true,false]) ++ (rep [false,false] (n)),([true,true,true])⟩ = some ⟨3,([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,false]) ++ (rep [false,false] (n)),([false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 3 ⟨3,([false,false,false,false]) ++ ([false,false,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,false]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (3*n) ⟨3,([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,false]) ++ (rep [false,false] (n)),([false])⟩ = some ⟨3,([false,false,false,false,true,false]) ++ (rep [false,false] (n)),(rep [true,true,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,false] [] [false,false,false] [true,true,true] 3 local5 n (([true,false]) ++ (rep [false,false] (n))) (([false]))

theorem phase6 (n : Nat) : run0 table 8 ⟨3,([false,false,false,false,true,false]) ++ (rep [false,false] (n)),(rep [true,true,true] (n)) ++ ([false])⟩ = some ⟨1,([true,true,false,false]) ++ (rep [false,false] (n)),([true,true]) ++ (rep [true,true,true] (n)) ++ ([false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 3 ⟨1,([true]) ++ (L),([true,true]) ++ ([true,true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([false,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (3*n) ⟨1,([true,true,false,false]) ++ (rep [false,false] (n)),([true,true]) ++ (rep [true,true,true] (n)) ++ ([false])⟩ = some ⟨1,([true]) ++ (rep [false,false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),([true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,true] [true,true,true] [false,false,false] 3 local7 n (([true,false,false]) ++ (rep [false,false] (n))) (([false]))

theorem phase8 (n : Nat) : run0 table 4 ⟨1,([true]) ++ (rep [false,false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),([true,true,false])⟩ = some ⟨2,([false,true,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)) = ([false,true,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (39+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 13+3*n+9+3*n+5+3*n+8+3*n+4=39+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 39+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M722

end BB6.Agent11Raw39RCPumps
