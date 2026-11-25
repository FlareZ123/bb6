import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B1RCPumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M1065

-- 1RB1RC_1RC1LE_0RD1LB_1LD0RA_1LF---_0LB1LB

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
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true,true])⟩

theorem entry : run0 table 14 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 3 ⟨4,[],([true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true,true])⟩ = some ⟨2,([false,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨2,([false]) ++ (L),([true,true]) ++ ([false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨2,([false,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true,true])⟩ = some ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true] [false,true,true] [true,false,false] 3 local1 n (([true])) (([true,true,true,true]))

theorem phase2 (n : Nat) : run0 table 4 ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true,true,true])⟩ = some ⟨1,([true,false,false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([true,false,false]) ++ ([true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,false]) ++ (L),([false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([true,false,false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true])⟩ = some ⟨1,([true,false,false,true]),(rep [false,true,true] (n)) ++ ([true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false] [] [true,false,false] [false,true,true] 3 local3 n (([true])) (([true,true,true,true]))

theorem phase4 (n : Nat) : run0 table 4 ⟨1,([true,false,false,true]),(rep [false,true,true] (n)) ++ ([true,true,true,true])⟩ = some ⟨4,[],([true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true,true]) = ([true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true,true]) := by
  rfl

theorem growth (n : Nat) : run0 table (11+6*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 3+3*n+4+3*n+4=11+6*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 14 (fun n => 11+6*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1065

namespace M1066

-- 1RB1RC_1RC1LE_0RD1LB_1LD0RA_1LF---_0LB1LC

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
  | 5,true => some (some ⟨true,false,2⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true])⟩

theorem entry : run0 table 18 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨1,[],([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true])⟩ = some ⟨2,([false,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨2,([false]) ++ (L),([true,true]) ++ ([false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨2,([false,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true])⟩ = some ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true] [false,true,true] [true,false,false] 3 local1 n (([true])) (([true,true]))

theorem phase2 (n : Nat) : run0 table 4 ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true])⟩ = some ⟨1,([true,false,false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([true,false,false]) ++ ([true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,false]) ++ (L),([false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([true,false,false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true])⟩ = some ⟨1,([true,false,false,true]),(rep [false,true,true] (n)) ++ ([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false] [] [true,false,false] [false,true,true] 3 local3 n (([true])) (([true,true]))

theorem phase4 (n : Nat) : run0 table 6 ⟨1,([true,false,false,true]),(rep [false,true,true] (n)) ++ ([true,true])⟩ = some ⟨1,[],([false,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true]) = ([false,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true]) := by
  rfl

theorem growth (n : Nat) : run0 table (11+6*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 1+3*n+4+3*n+6=11+6*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 18 (fun n => 11+6*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1066

namespace M1067

-- 1RB1RC_1RC1LE_0RD1LB_1LD0RA_1LF---_0LB1LE

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
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true])⟩

theorem entry : run0 table 11 ⟨0,[],[]⟩ = some (family 0) := by rfl

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
  never_of_growth table family 11 (fun n => 11+6*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1067

namespace M1068

-- 1RB1RC_1RC1LE_0RD1LB_1LD0RA_1LF---_0LB1LF

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
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true])⟩

theorem entry : run0 table 11 ⟨0,[],[]⟩ = some (family 0) := by rfl

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
  never_of_growth table family 11 (fun n => 11+6*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1068

namespace M1069

-- 1RB1RC_1RC1LE_0RD1LB_1LD0RA_1LF---_0LB1RC

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
  | 5,true => some (some ⟨true,true,2⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true])⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

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
  never_of_growth table family 13 (fun n => 11+6*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1069

namespace M1075

-- 1RB1RC_1RC1LE_0RD1LB_1LD0RA_1RF---_0LB1LF

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
  | 4,false => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true])⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨5,[],([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true])⟩ = some ⟨2,([false,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨2,([false]) ++ (L),([true,true]) ++ ([false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨2,([false,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true])⟩ = some ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true] [false,true,true] [true,false,false] 3 local1 n (([true])) (([true,true]))

theorem phase2 (n : Nat) : run0 table 4 ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true])⟩ = some ⟨1,([true,false,false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 5 ⟨1,([true,false,false]) ++ ([true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,false]) ++ (L),([false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (5*n) ⟨1,([true,false,false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true])⟩ = some ⟨1,([true,false,false,true]),(rep [false,true,true] (n)) ++ ([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false] [] [true,false,false] [false,true,true] 5 local3 n (([true])) (([true,true]))

theorem phase4 (n : Nat) : run0 table 9 ⟨1,([true,false,false,true]),(rep [false,true,true] (n)) ++ ([true,true])⟩ = some ⟨5,[],([true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true]) = ([true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true]) := by
  rfl

theorem growth (n : Nat) : run0 table (15+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 2+3*n+4+5*n+9=15+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 15+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1075

namespace M1078

-- 1RB1RC_1RC1LF_0RD1LB_1LD0RA_0LC0LA_0LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,2⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨false,false,4⟩)
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

end M1078

namespace M1082

-- 1RB1RC_1RC1LF_0RD1LB_1LD0RA_0LB0LB_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
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

end M1082

namespace M1084

-- 1RB1RC_1RC1LF_0RD1LB_1LD0RA_0LB0LE_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true,true])⟩

theorem entry : run0 table 21 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨4,[],([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true,true])⟩ = some ⟨2,([false,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨2,([false]) ++ (L),([true,true]) ++ ([false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨2,([false,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true,true])⟩ = some ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true] [false,true,true] [true,false,false] 3 local1 n (([true])) (([true,true,true,true]))

theorem phase2 (n : Nat) : run0 table 4 ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true,true,true])⟩ = some ⟨1,([true,false,false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([true,false,false]) ++ ([true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,false]) ++ (L),([false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([true,false,false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true])⟩ = some ⟨1,([true,false,false,true]),(rep [false,true,true] (n)) ++ ([true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false] [] [true,false,false] [false,true,true] 3 local3 n (([true])) (([true,true,true,true]))

theorem phase4 (n : Nat) : run0 table 5 ⟨1,([true,false,false,true]),(rep [false,true,true] (n)) ++ ([true,true,true,true])⟩ = some ⟨4,[],([true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true,true])⟩ := by rfl

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

end M1084

namespace M1085

-- 1RB1RC_1RC1LF_0RD1LB_1LD0RA_0LB0RA_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true])⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨4,[],([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true])⟩ = some ⟨2,([false,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨2,([false]) ++ (L),([true,true]) ++ ([false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨2,([false,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true])⟩ = some ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true] [false,true,true] [true,false,false] 3 local1 n (([true])) (([true,true]))

theorem phase2 (n : Nat) : run0 table 4 ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true,true,true])⟩ = some ⟨1,([true,false,false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([true,false,false]) ++ ([true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,false]) ++ (L),([false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([true,false,false]) ++ (rep [true,false,false] (n)) ++ ([true]),([true,true])⟩ = some ⟨1,([true,false,false,true]),(rep [false,true,true] (n)) ++ ([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false] [] [true,false,false] [false,true,true] 3 local3 n (([true])) (([true,true]))

theorem phase4 (n : Nat) : run0 table 5 ⟨1,([true,false,false,true]),(rep [false,true,true] (n)) ++ ([true,true])⟩ = some ⟨4,[],([true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true])⟩ := by rfl

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

end M1085

end BB6.Agent11Raw39B1RCPumps
