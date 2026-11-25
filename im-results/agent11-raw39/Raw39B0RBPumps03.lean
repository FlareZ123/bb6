import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B0RBPumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M144

-- 1RB0RB_1RC0LE_0RD0LD_1LD0RA_1LF1LC_1LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,false,2⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([true,true,false,true,true,false]) ++ (rep [true,true,false] (n))⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨1,[],([true,true,false,true,true,false]) ++ (rep [true,true,false] (n))⟩ = some ⟨2,([true,true]),([true,false,true,true,false]) ++ (rep [true,true,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 9 ⟨2,([true,true]) ++ (L),([true,false,true,true,false]) ++ ([true,true,false]) ++ (R)⟩ = some ⟨2,([true,true]) ++ ([true,false,false]) ++ (L),([true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (9*n) ⟨2,([true,true]),([true,false,true,true,false]) ++ (rep [true,true,false] (n))⟩ = some ⟨2,([true,true]) ++ (rep [true,false,false] (n)),([true,false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true,true] [true,false,true,true,false] [true,true,false] [true,false,false] 9 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 23 ⟨2,([true,true]) ++ (rep [true,false,false] (n)),([true,false,true,true,false])⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([true,false,false,true,false,false,true,false,false]) ++ ([true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (L),([true,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)),[]⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]),(rep [true,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false,true,false,false,true,false,false] [] [true,false,false] [true,true,false] 3 local3 n ([]) ([])

theorem phase4 (n : Nat) : run0 table 9 ⟨1,([true,false,false,true,false,false,true,false,false]),(rep [true,true,false] (n))⟩ = some ⟨1,[],([true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) = ([true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (33+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 1+9*n+23+3*n+9=33+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 33+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M144

namespace M145

-- 1RB0RB_1RC0LE_0RD0LE_1LD0RA_1LF0RA_1LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([true,true,false,true,true,false]) ++ (rep [true,true,false] (n))⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨1,[],([true,true,false,true,true,false]) ++ (rep [true,true,false] (n))⟩ = some ⟨2,([true,true]),([true,false,true,true,false]) ++ (rep [true,true,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 7 ⟨2,([true,true]) ++ (L),([true,false,true,true,false]) ++ ([true,true,false]) ++ (R)⟩ = some ⟨2,([true,true]) ++ ([true,false,false]) ++ (L),([true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (7*n) ⟨2,([true,true]),([true,false,true,true,false]) ++ (rep [true,true,false] (n))⟩ = some ⟨2,([true,true]) ++ (rep [true,false,false] (n)),([true,false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true,true] [true,false,true,true,false] [true,true,false] [true,false,false] 7 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 19 ⟨2,([true,true]) ++ (rep [true,false,false] (n)),([true,false,true,true,false])⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([true,false,false,true,false,false,true,false,false]) ++ ([true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (L),([true,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)),[]⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]),(rep [true,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false,true,false,false,true,false,false] [] [true,false,false] [true,true,false] 3 local3 n ([]) ([])

theorem phase4 (n : Nat) : run0 table 9 ⟨1,([true,false,false,true,false,false,true,false,false]),(rep [true,true,false] (n))⟩ = some ⟨1,[],([true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) = ([true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (29+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 1+7*n+19+3*n+9=29+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 29+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M145

namespace M148

-- 1RB0RB_1RC0LE_0RD0RD_1LD0RA_1LF0RB_1LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨1,([true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨1,([true,false,false,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨1,([true,false,false,true]) ++ (L),([true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨1,([true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨1,([true,false,false,true]),(rep [true,true,false,true,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false,true] [] [false,false,true,false,false,true] [true,true,false,true,true,false] 6 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 7 ⟨1,([true,false,false,true]),(rep [true,true,false,true,true,false] (n))⟩ = some ⟨2,([true,true]),([true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 30 ⟨2,([true]) ++ (L),([true,false,true,true,false]) ++ ([true,true,false,true,true,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,false,false,true,false,false]) ++ (L),([true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (30*n) ⟨2,([true,true]),([true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n))⟩ = some ⟨2,([true]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true,false,true,true,false] [true,true,false,true,true,false] [true,false,false,true,false,false] 30 local3 n (([true])) ([])

theorem phase4 (n : Nat) : run0 table 18 ⟨2,([true]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,true,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false])) ([]) [false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (31+36*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 6+6*n+7+30*n+18=31+36*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 31+36*n) entry (by intro n; omega) growth m hm

#print axioms never

end M148

namespace M149

-- 1RB0RB_1RC0LE_0RD0RD_1LD0RA_1LF0RF_1LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨1,([true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨1,([true,false,false,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨1,([true,false,false,true]) ++ (L),([true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨1,([true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨1,([true,false,false,true]),(rep [true,true,false,true,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false,true] [] [false,false,true,false,false,true] [true,true,false,true,true,false] 6 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 7 ⟨1,([true,false,false,true]),(rep [true,true,false,true,true,false] (n))⟩ = some ⟨2,([true,true]),([true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 14 ⟨2,([true]) ++ (L),([true,false,true,true,false]) ++ ([true,true,false,true,true,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,false,false,true,false,false]) ++ (L),([true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (14*n) ⟨2,([true,true]),([true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n))⟩ = some ⟨2,([true]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true,false,true,true,false] [true,true,false,true,true,false] [true,false,false,true,false,false] 14 local3 n (([true])) ([])

theorem phase4 (n : Nat) : run0 table 10 ⟨2,([true]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,true,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false])) ([]) [false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (23+20*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 6+6*n+7+14*n+10=23+20*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 23+20*n) entry (by intro n; omega) growth m hm

#print axioms never

end M149

namespace M152

-- 1RB0RB_1RC0LE_0RD1RC_1LD0RA_1LF0RE_1LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,4⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([false,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false])⟩

theorem entry : run0 table 96 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 3 ⟨4,[],([false,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false])⟩ = some ⟨2,([true,true]),([true,false,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 36 ⟨2,([true]) ++ (L),([true,false,true,true,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),([true,false,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (36*n) ⟨2,([true,true]),([true,false,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false])⟩ = some ⟨2,([true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([true,false,true,true,true,true,true,true,true,true,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true,false,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true] 36 local1 n (([true])) (([false]))

theorem phase2 (n : Nat) : run0 table 42 ⟨2,([true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([true,false,true,true,true,true,true,true,true,true,true,true,false])⟩ = some ⟨4,([false,false,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([false,true,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 24 ⟨4,([false,false,true,true,true,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,false,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (24*n) ⟨4,([false,false,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([false,true,true,false])⟩ = some ⟨4,([false,false,true,true,true,true,true,true,true,true,true,true,true,true]),(rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,false,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true] 24 local3 n (([true])) (([false,true,true,false]))

theorem phase4 (n : Nat) : run0 table 27 ⟨4,([false,false,true,true,true,true,true,true,true,true,true,true,true,true]),(rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,true,true,false])⟩ = some ⟨2,([true,true]),([true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,true,true,false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 12 ⟨2,([true]) ++ (L),([true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (12*n) ⟨2,([true,true]),([true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false,true,true,false])⟩ = some ⟨2,([true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true] 12 local5 n (([true])) (([false,true,true,false]))

theorem phase6 (n : Nat) : run0 table 75 ⟨2,([true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,false])⟩ = some ⟨4,([false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 24 ⟨4,([false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (24*n) ⟨4,([false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([false])⟩ = some ⟨4,([false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),(rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true] 24 local7 n (([true])) (([false]))

theorem phase8 (n : Nat) : run0 table 43 ⟨4,([false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),(rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false])⟩ = some ⟨4,[],([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false]) = ([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([false]) := by
  rfl

theorem growth (n : Nat) : run0 table (190+96*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 3+36*n+42+24*n+27+12*n+75+24*n+43=190+96*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 96 (fun n => 190+96*n) entry (by intro n; omega) growth m hm

#print axioms never

end M152

namespace M159

-- 1RB0RB_1RC0LE_0RD0LA_1LD0RA_1LF0LA_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,([false,false,true]) ++ (rep [false,false] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 3 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 5 ⟨3,([false,false,true]) ++ (rep [false,false] (n)) ++ ([true]),[]⟩ = some ⟨4,([false,false]) ++ (rep [false,false] (n)) ++ ([true]),([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨4,([false,false]) ++ ([false,false]) ++ (L),(R)⟩ = some ⟨4,([false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨4,([false,false]) ++ (rep [false,false] (n)) ++ ([true]),([false])⟩ = some ⟨4,([false,false,true]),(rep [true,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,false] [] [false,false] [true,true] 2 local1 n (([true])) (([false]))

theorem phase2 (n : Nat) : run0 table 4 ⟨4,([false,false,true]),(rep [true,true] (n)) ++ ([false])⟩ = some ⟨1,([false,true]),([true,true]) ++ (rep [true,true] (n)) ++ ([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨1,([false]) ++ (L),([true,true]) ++ ([true,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨1,([false,true]),([true,true]) ++ (rep [true,true] (n)) ++ ([false])⟩ = some ⟨1,([false]) ++ (rep [false,false] (n)) ++ ([true]),([true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,true] [true,true] [false,false] 6 local3 n (([true])) (([false]))

theorem phase4 (n : Nat) : run0 table 8 ⟨1,([false]) ++ (rep [false,false] (n)) ++ ([true]),([true,true,false])⟩ = some ⟨3,([false,false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true]) = ([false,false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (17+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 5+2*n+4+6*n+8=17+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 3 (fun n => 17+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M159

namespace M198

-- 1RB0RB_1RC0LF_0RD0LD_1LD0RA_1LB---_0LE1RD

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨true,true,3⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩

theorem entry : run0 table 12 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 3 ⟨4,[],([false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨3,([true]) ++ (L),([false,false,false,true,false,false]) ++ ([false,true,false,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,false]) ++ (L),([false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨3,([true]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,true,false] (n)),([false,false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,false,false,true,false,false] [false,true,false,false] [false,true,true,false] 4 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 8 ⟨3,([true]) ++ (rep [false,true,true,false] (n)),([false,false,false,true,false,false])⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 24 ⟨3,([false,false,true,true,false,false,true,true,false]) ++ ([false,true,true,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (L),([false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (24*n) ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)),[]⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]),(rep [false,true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true,false,false,true,true,false] [] [false,true,true,false] [false,true,false,false] 24 local3 n ([]) ([])

theorem phase4 (n : Nat) : run0 table 33 ⟨3,([false,false,true,true,false,false,true,true,false]),(rep [false,true,false,false] (n))⟩ = some ⟨4,[],([false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) = ([false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (44+28*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 3+4*n+8+24*n+33=44+28*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 12 (fun n => 44+28*n) entry (by intro n; omega) growth m hm

#print axioms never

end M198

namespace M199

-- 1RB0RB_1RC0LF_0RD0RA_1LD0RA_1LB0RF_0LE---

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
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([true,false,false,true,false,false]) ++ (rep [true,false,false] (n))⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨1,[],([true,false,false,true,false,false]) ++ (rep [true,false,false] (n))⟩ = some ⟨2,([true,true]),([false,false,true,false,false]) ++ (rep [true,false,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨2,([true]) ++ (L),([false,false,true,false,false]) ++ ([true,false,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true,false]) ++ (L),([false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨2,([true,true]),([false,false,true,false,false]) ++ (rep [true,false,false] (n))⟩ = some ⟨2,([true]) ++ (rep [true,true,false] (n)) ++ ([true]),([false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,false,true,false,false] [true,false,false] [true,true,false] 3 local1 n (([true])) ([])

theorem phase2 (n : Nat) : run0 table 12 ⟨2,([true]) ++ (rep [true,true,false] (n)) ++ ([true]),([false,false,true,false,false])⟩ = some ⟨5,([false,false,true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true]),([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 5 ⟨5,([false,false,true,false,true,true,false]) ++ ([true,true,false]) ++ (L),(R)⟩ = some ⟨5,([false,false,true,false,true,true,false]) ++ (L),([false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (5*n) ⟨5,([false,false,true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true]),([false])⟩ = some ⟨5,([false,false,true,false,true,true,false,true]),(rep [false,true,false] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,true,false,true,true,false] [] [true,true,false] [false,true,false] 5 local3 n (([true])) (([false]))

theorem phase4 (n : Nat) : run0 table 12 ⟨5,([false,false,true,false,true,true,false,true]),(rep [false,true,false] (n)) ++ ([false])⟩ = some ⟨1,[],([true,false,false,true,false,false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,false,true,false,false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false]) = ([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) := by
  calc
    _ = ([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,false,true,false,false,true,false])) ([]) [true,false] false n

theorem growth (n : Nat) : run0 table (25+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 1+3*n+12+5*n+12=25+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 25+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M199

namespace M200

-- 1RB0RB_1RC0LF_0RD0RA_1LD0RA_1LB1LB_0LE---

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
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([true,false,false,true,false,false]) ++ (rep [true,false,false] (n))⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨1,[],([true,false,false,true,false,false]) ++ (rep [true,false,false] (n))⟩ = some ⟨2,([true,true]),([false,false,true,false,false]) ++ (rep [true,false,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨2,([true]) ++ (L),([false,false,true,false,false]) ++ ([true,false,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true,false]) ++ (L),([false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨2,([true,true]),([false,false,true,false,false]) ++ (rep [true,false,false] (n))⟩ = some ⟨2,([true]) ++ (rep [true,true,false] (n)) ++ ([true]),([false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,false,true,false,false] [true,false,false] [true,true,false] 3 local1 n (([true])) ([])

theorem phase2 (n : Nat) : run0 table 14 ⟨2,([true]) ++ (rep [true,true,false] (n)) ++ ([true]),([false,false,true,false,false])⟩ = some ⟨1,([true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true]),([true,false,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([true,false,true,true,false]) ++ ([true,true,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,true,true,false]) ++ (L),([true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true]),([true,false,false])⟩ = some ⟨1,([true,false,true,true,false,true]),(rep [true,false,false] (n)) ++ ([true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,true,true,false] [] [true,true,false] [true,false,false] 3 local3 n (([true])) (([true,false,false]))

theorem phase4 (n : Nat) : run0 table 6 ⟨1,([true,false,true,true,false,true]),(rep [true,false,false] (n)) ++ ([true,false,false])⟩ = some ⟨1,[],([true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([true,false,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([true,false,false]) = ([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) := by
  calc
    _ = ([true,false,false,true,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([false,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,false,true,false,false])) (([false,false])) [false,false] true n
    _ = ([true,false,false,true,false,false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,false,true,false,false,true])) (([false])) [false,true] false n
    _ = ([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,false,true,false,false,true,false])) ([]) [true,false] false n

theorem growth (n : Nat) : run0 table (21+6*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 1+3*n+14+3*n+6=21+6*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 21+6*n) entry (by intro n; omega) growth m hm

#print axioms never

end M200

namespace M201

-- 1RB0RB_1RC0LF_0RD0RA_1LD0RA_1LB1RC_0LE---

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
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,true,2⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([true,false,false,true,false,false]) ++ (rep [true,false,false] (n))⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨1,[],([true,false,false,true,false,false]) ++ (rep [true,false,false] (n))⟩ = some ⟨2,([true,true]),([false,false,true,false,false]) ++ (rep [true,false,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨2,([true]) ++ (L),([false,false,true,false,false]) ++ ([true,false,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true,false]) ++ (L),([false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨2,([true,true]),([false,false,true,false,false]) ++ (rep [true,false,false] (n))⟩ = some ⟨2,([true]) ++ (rep [true,true,false] (n)) ++ ([true]),([false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,false,true,false,false] [true,false,false] [true,true,false] 3 local1 n (([true])) ([])

theorem phase2 (n : Nat) : run0 table 7 ⟨2,([true]) ++ (rep [true,true,false] (n)) ++ ([true]),([false,false,true,false,false])⟩ = some ⟨3,([false,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 11 ⟨3,([false,false,true,true,false,true,true,false]) ++ ([true,true,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true,false,true,true,false]) ++ (L),([true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (11*n) ⟨3,([false,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true]),[]⟩ = some ⟨3,([false,false,true,true,false,true,true,false,true]),(rep [true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true,false,true,true,false] [] [true,true,false] [true,false,false] 11 local3 n (([true])) ([])

theorem phase4 (n : Nat) : run0 table 29 ⟨3,([false,false,true,true,false,true,true,false,true]),(rep [true,false,false] (n))⟩ = some ⟨1,[],([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) = ([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (37+14*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 1+3*n+7+11*n+29=37+14*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 37+14*n) entry (by intro n; omega) growth m hm

#print axioms never

end M201

end BB6.Agent11Raw39B0RBPumps
