import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B0RBPumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M119

-- 1RB0RB_1RC0LE_0RD0RF_1LD0RA_1LF0RB_0LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,false => some (some ⟨false,false,1⟩)
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

end M119

namespace M120

-- 1RB0RB_1RC0LE_0RD1LA_1LD0RA_1LF---_0LB0RF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨false,true,5⟩)
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

end M120

namespace M121

-- 1RB0RB_1RC0LE_0RD1LB_1LD0RA_1LF0RB_0LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,false => some (some ⟨false,false,1⟩)
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

end M121

namespace M122

-- 1RB0RB_1RC0LE_0RD1LB_1LD0RA_1LF0RF_0LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
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

end M122

namespace M124

-- 1RB0RB_1RC0LE_0RD1LD_1LD0RA_1LF---_0LB0LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨false,false,1⟩)
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

end M124

namespace M127

-- 1RB0RB_1RC0LE_0RD1RA_1LD0RA_1LF0RD_0LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,3⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩

theorem entry : run0 table 11 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 5 ⟨4,[],([false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ = some ⟨0,([false,false,false,true]),([false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨0,([false]) ++ (L),([false,true,false]) ++ ([false,true,false,false,true,false]) ++ (R)⟩ = some ⟨0,([false]) ++ ([true,true,true,true,true,true]) ++ (L),([false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨0,([false,false,false,true]),([false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ = some ⟨0,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false,false,true]),([false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [false] [false,true,false] [false,true,false,false,true,false] [true,true,true,true,true,true] 6 local1 n (([false,false,true])) ([])

theorem phase2 (n : Nat) : run0 table 6 ⟨0,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false,false,true]),([false,true,false])⟩ = some ⟨3,([false,false,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false,false,true]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 18 ⟨3,([false,false,true,true,true,true,true]) ++ ([true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true,true,true,true]) ++ (L),([false,true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (18*n) ⟨3,([false,false,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false,false,true]),[]⟩ = some ⟨3,([false,false,true,true,true,true,true,false,false,true]),(rep [false,true,false,false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true,true,true,true] [] [true,true,true,true,true,true] [false,true,false,false,true,false] 18 local3 n (([false,false,true])) ([])

theorem phase4 (n : Nat) : run0 table 20 ⟨3,([false,false,true,true,true,true,true,false,false,true]),(rep [false,true,false,false,true,false] (n))⟩ = some ⟨4,[],([false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) = ([false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (31+24*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 5+6*n+6+18*n+20=31+24*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 11 (fun n => 31+24*n) entry (by intro n; omega) growth m hm

#print axioms never

end M127

namespace M128

-- 1RB0RB_1RC0LE_0RD1RC_1LD0RA_1LF0RB_0LB---

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
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false,true]) ++ (rep [true] (n)),[]⟩

theorem entry : run0 table 33 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false,true]) ++ (rep [true] (n)),[]⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false,true]) ++ (rep [true] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨1,([true,false,false,true,false,false,true,false,false]) ++ ([true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (L),([false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false,true]) ++ (rep [true] (n)),[]⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false,false,true]) ++ (rep [true] (n)),(rep [false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false,true,false,false,true,false,false] [] [true,false,false] [false,true,false] 3 local1 n (([false,true]) ++ (rep [true] (n))) ([])

theorem phase2 (n : Nat) : run0 table 25 ⟨1,([true,false,false,true,false,false,true,false,false,false,true]) ++ (rep [true] (n)),(rep [false,true,false] (n))⟩ = some ⟨1,([false,false,false,false,true,true]) ++ (rep [true] (n)),([false,true,false,true,false]) ++ (rep [false,true,false] (n))⟩ := by rfl

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

theorem growth (n : Nat) : run0 table (50+18*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 6+3*n+25+15*n+19=50+18*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 33 (fun n => 50+18*n) entry (by intro n; omega) growth m hm

#print axioms never

end M128

namespace M130

-- 1RB0RB_1RC0LE_0RD1RF_1LD0RA_1LF0LA_0LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨1,([true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨1,([true,false,false,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨1,([true,false,false,true]) ++ (L),([false,true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨1,([true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨1,([true,false,false,true]),(rep [false,true,false,false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false,true] [] [false,false,true,false,false,true] [false,true,false,false,true,false] 6 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 7 ⟨1,([true,false,false,true]),(rep [false,true,false,false,true,false] (n))⟩ = some ⟨2,([false,true]),([true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 38 ⟨2,([false]) ++ (L),([true,false,false,true,false]) ++ ([false,true,false,false,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (38*n) ⟨2,([false,true]),([true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true,false] [false,true,false,false,true,false] [true,false,false,true,false,false] 38 local3 n (([true])) ([])

theorem phase4 (n : Nat) : run0 table 22 ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false])) ([]) [false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (35+44*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 6+6*n+7+38*n+22=35+44*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 35+44*n) entry (by intro n; omega) growth m hm

#print axioms never

end M130

namespace M142

-- 1RB0RB_1RC0LE_0RD0LD_1LD0RA_1LF0RA_1LB---

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

end M142

namespace M143

-- 1RB0RB_1RC0LE_0RD0LD_1LD0RA_1LF0RF_1LB---

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
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([true,true,false,true,true,false]) ++ (rep [true,true,false] (n))⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨1,[],([true,true,false,true,true,false]) ++ (rep [true,true,false] (n))⟩ = some ⟨2,([true,true]),([true,false,true,true,false]) ++ (rep [true,true,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 11 ⟨2,([true,true]) ++ (L),([true,false,true,true,false]) ++ ([true,true,false]) ++ (R)⟩ = some ⟨2,([true,true]) ++ ([true,false,false]) ++ (L),([true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (11*n) ⟨2,([true,true]),([true,false,true,true,false]) ++ (rep [true,true,false] (n))⟩ = some ⟨2,([true,true]) ++ (rep [true,false,false] (n)),([true,false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true,true] [true,false,true,true,false] [true,true,false] [true,false,false] 11 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 27 ⟨2,([true,true]) ++ (rep [true,false,false] (n)),([true,false,true,true,false])⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([true,false,false,true,false,false,true,false,false]) ++ ([true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (L),([true,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)),[]⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]),(rep [true,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false,true,false,false,true,false,false] [] [true,false,false] [true,true,false] 3 local3 n ([]) ([])

theorem phase4 (n : Nat) : run0 table 9 ⟨1,([true,false,false,true,false,false,true,false,false]),(rep [true,true,false] (n))⟩ = some ⟨1,[],([true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) = ([true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (37+14*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 1+11*n+27+3*n+9=37+14*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 37+14*n) entry (by intro n; omega) growth m hm

#print axioms never

end M143

end BB6.Agent11Raw39B0RBPumps
