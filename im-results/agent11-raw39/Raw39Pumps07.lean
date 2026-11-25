import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39Pumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M828

-- 1RB1RB_1RC0RE_0RD0LF_1LD0RA_1RF---_1LC1RF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨true,true,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,([false,true,true,true,true]) ++ (rep [true] (n)) ++ ([false,true,false,false]),[]⟩

theorem entry : run0 table 38 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 3 ⟨5,([false,true,true,true,true]) ++ ([true]) ++ (L),(R)⟩ = some ⟨5,([false,true,true,true,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (3*n) ⟨5,([false,true,true,true,true]) ++ (rep [true] (n)) ++ ([false,true,false,false]),[]⟩ = some ⟨5,([false,true,true,true,true,false,true,false,false]),(rep [true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true,true,true,true] [] [true] [true] 3 local0 n (([false,true,false,false])) ([])

theorem phase1 (n : Nat) : run0 table 19 ⟨5,([false,true,true,true,true,false,true,false,false]),(rep [true] (n))⟩ = some ⟨5,([true,true,false,true,false,false]),([true,true,true]) ++ (rep [true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 1 ⟨5,([true]) ++ (L),([true,true,true]) ++ ([true]) ++ (R)⟩ = some ⟨5,([true]) ++ ([true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (1*n) ⟨5,([true,true,false,true,false,false]),([true,true,true]) ++ (rep [true] (n))⟩ = some ⟨5,([true]) ++ (rep [true] (n)) ++ ([true,false,true,false,false]),([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 5 [true] [true,true,true] [true] [true] 1 local2 n (([true,false,true,false,false])) ([])

theorem phase3 (n : Nat) : run0 table 4 ⟨5,([true]) ++ (rep [true] (n)) ++ ([true,false,true,false,false]),([true,true,true])⟩ = some ⟨5,([false,true,true,true,true]) ++ (rep [true] (n)) ++ ([true,false,true,false,false]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true]) ++ (rep [true] (n)) ++ ([true,false,true,false,false]) = ([false,true,true,true,true,true]) ++ (rep [true] (n)) ++ ([false,true,false,false]) := by
  calc
    _ = ([false,true,true,true,true,true]) ++ (rep [true] (n)) ++ ([false,true,false,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,true])) (([false,true,false,false])) [] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (23+4*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 3*n+19+1*n+4=23+4*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 38 (fun n => 23+4*n) entry (by intro n; omega) growth m hm

#print axioms never

end M828

namespace M1141

-- 1RB1RB_1RC0RF_0RD0LE_1LD0RA_1LC1RE_1RE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,true,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false,true,true,true,true]) ++ (rep [true] (n)) ++ ([false,true,false,false]),[]⟩

theorem entry : run0 table 38 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 3 ⟨4,([false,true,true,true,true]) ++ ([true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true,true,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (3*n) ⟨4,([false,true,true,true,true]) ++ (rep [true] (n)) ++ ([false,true,false,false]),[]⟩ = some ⟨4,([false,true,true,true,true,false,true,false,false]),(rep [true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true,true,true] [] [true] [true] 3 local0 n (([false,true,false,false])) ([])

theorem phase1 (n : Nat) : run0 table 19 ⟨4,([false,true,true,true,true,false,true,false,false]),(rep [true] (n))⟩ = some ⟨4,([true,true,false,true,false,false]),([true,true,true]) ++ (rep [true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 1 ⟨4,([true]) ++ (L),([true,true,true]) ++ ([true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (1*n) ⟨4,([true,true,false,true,false,false]),([true,true,true]) ++ (rep [true] (n))⟩ = some ⟨4,([true]) ++ (rep [true] (n)) ++ ([true,false,true,false,false]),([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true,true,true] [true] [true] 1 local2 n (([true,false,true,false,false])) ([])

theorem phase3 (n : Nat) : run0 table 4 ⟨4,([true]) ++ (rep [true] (n)) ++ ([true,false,true,false,false]),([true,true,true])⟩ = some ⟨4,([false,true,true,true,true]) ++ (rep [true] (n)) ++ ([true,false,true,false,false]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true]) ++ (rep [true] (n)) ++ ([true,false,true,false,false]) = ([false,true,true,true,true,true]) ++ (rep [true] (n)) ++ ([false,true,false,false]) := by
  calc
    _ = ([false,true,true,true,true,true]) ++ (rep [true] (n)) ++ ([false,true,false,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,true])) (([false,true,false,false])) [] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (23+4*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 3*n+19+1*n+4=23+4*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 38 (fun n => 23+4*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1141

namespace M1550

-- 1RB1RB_1RC1LE_0RD1RF_1LD0RA_0LB0LE_1RD---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([false,true,false,false,true,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([false,false,true,false,false,true])⟩

theorem entry : run0 table 76 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 37 ⟨1,[],([false,true,false,false,true,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([false,false,true,false,false,true])⟩ = some ⟨1,([false,true,false,true,true,true,true,false,false,true]),([true]) ++ (rep [false,false,false,true] (n)) ++ ([false,false,true,false,false,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨1,([false]) ++ (L),([true]) ++ ([false,false,false,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,false,true,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨1,([false,true,false,true,true,true,true,false,false,true]),([true]) ++ (rep [false,false,false,true] (n)) ++ ([false,false,true,false,false,true])⟩ = some ⟨1,([false]) ++ (rep [true,false,true,true] (n)) ++ ([true,false,true,true,true,true,false,false,true]),([true,false,false,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true] [false,false,false,true] [true,false,true,true] 6 local1 n (([true,false,true,true,true,true,false,false,true])) (([false,false,true,false,false,true]))

theorem phase2 (n : Nat) : run0 table 7 ⟨1,([false]) ++ (rep [true,false,true,true] (n)) ++ ([true,false,true,true,true,true,false,false,true]),([true,false,false,true,false,false,true])⟩ = some ⟨4,([true,false,true,true]) ++ (rep [true,false,true,true] (n)) ++ ([true,false,true,true,true,true,false,false,true]),([true,false,false,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 4 ⟨4,([true,false,true,true]) ++ ([true,false,true,true]) ++ (L),(R)⟩ = some ⟨4,([true,false,true,true]) ++ (L),([false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (4*n) ⟨4,([true,false,true,true]) ++ (rep [true,false,true,true] (n)) ++ ([true,false,true,true,true,true,false,false,true]),([true,false,false,true])⟩ = some ⟨4,([true,false,true,true,true,false,true,true,true,true,false,false,true]),(rep [false,true,false,false] (n)) ++ ([true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,true,true] [] [true,false,true,true] [false,true,false,false] 4 local3 n (([true,false,true,true,true,true,false,false,true])) (([true,false,false,true]))

theorem phase4 (n : Nat) : run0 table 22 ⟨4,([true,false,true,true,true,false,true,true,true,true,false,false,true]),(rep [false,true,false,false] (n)) ++ ([true,false,false,true])⟩ = some ⟨1,[],([false,true,false,false,true,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) ++ ([true,false,false,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,true,false,false,true,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) ++ ([true,false,false,true]) = ([false,true,false,false,true,false,false,true,false,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([false,false,true,false,false,true]) := by
  calc
    _ = ([false,true,false,false,true,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false] (n)) ++ ([false,true,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false,true,false,false,false,true,false])) (([true,false,false,true])) [false,true,false] false n
    _ = ([false,true,false,false,true,false,false,true,false,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([false,false,true,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false,true,false,false,false,true])) (([false,true,false,false,true])) [false,false,true] false n

theorem growth (n : Nat) : run0 table (66+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 37+6*n+7+4*n+22=66+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 76 (fun n => 66+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1550

namespace M1607

-- 1RB1RB_1RC1LE_0RD0RA_1LD0RA_0LB0LF_1LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,([false,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,false,true]),[]⟩

theorem entry : run0 table 21 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 9 ⟨3,([false,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,false,true]),[]⟩ = some ⟨1,([true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,false,true]),([false,true,true,false,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 12 ⟨1,([true,true]) ++ ([false,true,true,false,true,true,false,true,true,false,true,true]) ++ (L),(R)⟩ = some ⟨1,([true,true]) ++ (L),([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (12*n) ⟨1,([true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,false,true]),([false,true,true,false,true])⟩ = some ⟨1,([true,true,false,false,true]),(rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([false,true,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true] [] [false,true,true,false,true,true,false,true,true,false,true,true] [true,false,true,true,false,true,true,false,true,true,false,true] 12 local1 n (([false,false,true])) (([false,true,true,false,true]))

theorem phase2 (n : Nat) : run0 table 23 ⟨1,([true,true,false,false,true]),(rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([false,true,true,false,true])⟩ = some ⟨0,([true,false,false,true]),([false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([false,true,true,false,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 12 ⟨0,([true]) ++ (L),([false,true,true,false,true]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (R)⟩ = some ⟨0,([true]) ++ ([false,true,true,false,true,true,false,true,true,false,true,true]) ++ (L),([false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (12*n) ⟨0,([true,false,false,true]),([false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([false,true,true,false,true])⟩ = some ⟨0,([true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,false,true]),([false,true,true,false,true,false,true,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [true] [false,true,true,false,true] [true,false,true,true,false,true,true,false,true,true,false,true] [false,true,true,false,true,true,false,true,true,false,true,true] 12 local3 n (([false,false,true])) (([false,true,true,false,true]))

theorem phase4 (n : Nat) : run0 table 7 ⟨0,([true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,false,true]),([false,true,true,false,true,false,true,true,false,true])⟩ = some ⟨1,([true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,false,true]),([true,false,true])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 12 ⟨1,([true,true,false,true,true,false,true,true]) ++ ([false,true,true,false,true,true,false,true,true,false,true,true]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,true,true,false,true,true]) ++ (L),([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (12*n) ⟨1,([true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,false,true]),([true,false,true])⟩ = some ⟨1,([true,true,false,true,true,false,true,true,false,false,true]),(rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,true,true,false,true,true] [] [false,true,true,false,true,true,false,true,true,false,true,true] [true,false,true,true,false,true,true,false,true,true,false,true] 12 local5 n (([false,false,true])) (([true,false,true]))

theorem phase6 (n : Nat) : run0 table 29 ⟨1,([true,true,false,true,true,false,true,true,false,false,true]),(rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true,false,true])⟩ = some ⟨0,([true,false,false,true]),([false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true,false,true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 12 ⟨0,([true]) ++ (L),([false,true,true,false,true,true,false,true,true,false,true]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (R)⟩ = some ⟨0,([true]) ++ ([false,true,true,false,true,true,false,true,true,false,true,true]) ++ (L),([false,true,true,false,true,true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (12*n) ⟨0,([true,false,false,true]),([false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true,false,true])⟩ = some ⟨0,([true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,false,true]),([false,true,true,false,true,true,false,true,true,false,true,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [true] [false,true,true,false,true,true,false,true,true,false,true] [true,false,true,true,false,true,true,false,true,true,false,true] [false,true,true,false,true,true,false,true,true,false,true,true] 12 local7 n (([false,false,true])) (([true,false,true]))

theorem phase8 (n : Nat) : run0 table 18 ⟨0,([true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,false,true]),([false,true,true,false,true,true,false,true,true,false,true,true,false,true])⟩ = some ⟨3,([false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,false,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,false,true]) = ([false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,false,true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (86+48*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 9+12*n+23+12*n+7+12*n+29+12*n+18=86+48*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 21 (fun n => 86+48*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1607

namespace M1945

-- 1RB1RB_1RC1LF_0RD0RA_1LD0RA_1LB---_0LB0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,([false,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,false,true]),[]⟩

theorem entry : run0 table 21 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 9 ⟨3,([false,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,false,true]),[]⟩ = some ⟨1,([true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,false,true]),([false,true,true,false,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 12 ⟨1,([true,true]) ++ ([false,true,true,false,true,true,false,true,true,false,true,true]) ++ (L),(R)⟩ = some ⟨1,([true,true]) ++ (L),([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (12*n) ⟨1,([true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,false,true]),([false,true,true,false,true])⟩ = some ⟨1,([true,true,false,false,true]),(rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([false,true,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true] [] [false,true,true,false,true,true,false,true,true,false,true,true] [true,false,true,true,false,true,true,false,true,true,false,true] 12 local1 n (([false,false,true])) (([false,true,true,false,true]))

theorem phase2 (n : Nat) : run0 table 23 ⟨1,([true,true,false,false,true]),(rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([false,true,true,false,true])⟩ = some ⟨0,([true,false,false,true]),([false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([false,true,true,false,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 12 ⟨0,([true]) ++ (L),([false,true,true,false,true]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (R)⟩ = some ⟨0,([true]) ++ ([false,true,true,false,true,true,false,true,true,false,true,true]) ++ (L),([false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (12*n) ⟨0,([true,false,false,true]),([false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([false,true,true,false,true])⟩ = some ⟨0,([true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,false,true]),([false,true,true,false,true,false,true,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [true] [false,true,true,false,true] [true,false,true,true,false,true,true,false,true,true,false,true] [false,true,true,false,true,true,false,true,true,false,true,true] 12 local3 n (([false,false,true])) (([false,true,true,false,true]))

theorem phase4 (n : Nat) : run0 table 7 ⟨0,([true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,false,true]),([false,true,true,false,true,false,true,true,false,true])⟩ = some ⟨1,([true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,false,true]),([true,false,true])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 12 ⟨1,([true,true,false,true,true,false,true,true]) ++ ([false,true,true,false,true,true,false,true,true,false,true,true]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,true,true,false,true,true]) ++ (L),([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (12*n) ⟨1,([true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,false,true]),([true,false,true])⟩ = some ⟨1,([true,true,false,true,true,false,true,true,false,false,true]),(rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,true,true,false,true,true] [] [false,true,true,false,true,true,false,true,true,false,true,true] [true,false,true,true,false,true,true,false,true,true,false,true] 12 local5 n (([false,false,true])) (([true,false,true]))

theorem phase6 (n : Nat) : run0 table 29 ⟨1,([true,true,false,true,true,false,true,true,false,false,true]),(rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true,false,true])⟩ = some ⟨0,([true,false,false,true]),([false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true,false,true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 12 ⟨0,([true]) ++ (L),([false,true,true,false,true,true,false,true,true,false,true]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (R)⟩ = some ⟨0,([true]) ++ ([false,true,true,false,true,true,false,true,true,false,true,true]) ++ (L),([false,true,true,false,true,true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (12*n) ⟨0,([true,false,false,true]),([false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true,false,true])⟩ = some ⟨0,([true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,false,true]),([false,true,true,false,true,true,false,true,true,false,true,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [true] [false,true,true,false,true,true,false,true,true,false,true] [true,false,true,true,false,true,true,false,true,true,false,true] [false,true,true,false,true,true,false,true,true,false,true,true] 12 local7 n (([false,false,true])) (([true,false,true]))

theorem phase8 (n : Nat) : run0 table 18 ⟨0,([true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,false,true]),([false,true,true,false,true,true,false,true,true,false,true,true,false,true])⟩ = some ⟨3,([false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,false,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,false,true]) = ([false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,false,true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (86+48*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 9+12*n+23+12*n+7+12*n+29+12*n+18=86+48*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 21 (fun n => 86+48*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1945

namespace M1997

-- 1RB1RB_1RC1LF_0RD1RE_1LD0RA_1RD---_0LB0LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,true,3⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([false,true,false,false,true,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([false,false,true,false,false,true])⟩

theorem entry : run0 table 76 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 37 ⟨1,[],([false,true,false,false,true,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([false,false,true,false,false,true])⟩ = some ⟨1,([false,true,false,true,true,true,true,false,false,true]),([true]) ++ (rep [false,false,false,true] (n)) ++ ([false,false,true,false,false,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨1,([false]) ++ (L),([true]) ++ ([false,false,false,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,false,true,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨1,([false,true,false,true,true,true,true,false,false,true]),([true]) ++ (rep [false,false,false,true] (n)) ++ ([false,false,true,false,false,true])⟩ = some ⟨1,([false]) ++ (rep [true,false,true,true] (n)) ++ ([true,false,true,true,true,true,false,false,true]),([true,false,false,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true] [false,false,false,true] [true,false,true,true] 6 local1 n (([true,false,true,true,true,true,false,false,true])) (([false,false,true,false,false,true]))

theorem phase2 (n : Nat) : run0 table 7 ⟨1,([false]) ++ (rep [true,false,true,true] (n)) ++ ([true,false,true,true,true,true,false,false,true]),([true,false,false,true,false,false,true])⟩ = some ⟨5,([true,false,true,true]) ++ (rep [true,false,true,true] (n)) ++ ([true,false,true,true,true,true,false,false,true]),([true,false,false,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 4 ⟨5,([true,false,true,true]) ++ ([true,false,true,true]) ++ (L),(R)⟩ = some ⟨5,([true,false,true,true]) ++ (L),([false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (4*n) ⟨5,([true,false,true,true]) ++ (rep [true,false,true,true] (n)) ++ ([true,false,true,true,true,true,false,false,true]),([true,false,false,true])⟩ = some ⟨5,([true,false,true,true,true,false,true,true,true,true,false,false,true]),(rep [false,true,false,false] (n)) ++ ([true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,false,true,true] [] [true,false,true,true] [false,true,false,false] 4 local3 n (([true,false,true,true,true,true,false,false,true])) (([true,false,false,true]))

theorem phase4 (n : Nat) : run0 table 22 ⟨5,([true,false,true,true,true,false,true,true,true,true,false,false,true]),(rep [false,true,false,false] (n)) ++ ([true,false,false,true])⟩ = some ⟨1,[],([false,true,false,false,true,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) ++ ([true,false,false,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,true,false,false,true,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) ++ ([true,false,false,true]) = ([false,true,false,false,true,false,false,true,false,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([false,false,true,false,false,true]) := by
  calc
    _ = ([false,true,false,false,true,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false] (n)) ++ ([false,true,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false,true,false,false,false,true,false])) (([true,false,false,true])) [false,true,false] false n
    _ = ([false,true,false,false,true,false,false,true,false,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([false,false,true,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false,true,false,false,false,true])) (([false,true,false,false,true])) [false,false,true] false n

theorem growth (n : Nat) : run0 table (66+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 37+6*n+7+4*n+22=66+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 76 (fun n => 66+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1997

namespace M2288

-- 1RB1RB_1RC1RE_0RD---_1LD0RA_0LF1RA_0LB1LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false,false,true]) ++ (rep [true] (n)),[]⟩

theorem entry : run0 table 23 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 13 ⟨1,([false,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false,false,true]) ++ (rep [true] (n)),[]⟩ = some ⟨5,([true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false,false,true]) ++ (rep [true] (n)),([false,true,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨5,([true,true,true,true]) ++ ([true,true,true]) ++ (L),(R)⟩ = some ⟨5,([true,true,true,true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨5,([true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false,false,true]) ++ (rep [true] (n)),([false,true,true,false])⟩ = some ⟨5,([true,true,true,true,false,false,true]) ++ (rep [true] (n)),(rep [true,true,true] (n)) ++ ([false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,true,true,true] [] [true,true,true] [true,true,true] 3 local1 n (([false,false,true]) ++ (rep [true] (n))) (([false,true,true,false]))

theorem phase2 (n : Nat) : run0 table 8 ⟨5,([true,true,true,true,false,false,true]) ++ (rep [true] (n)),(rep [true,true,true] (n)) ++ ([false,true,true,false])⟩ = some ⟨0,([true,false,false,true,true]) ++ (rep [true] (n)),([true,true]) ++ (rep [true,true,true] (n)) ++ ([false,true,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨0,([true]) ++ (L),([true,true]) ++ ([true,true,true]) ++ (R)⟩ = some ⟨0,([true]) ++ ([true,true,true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨0,([true,false,false,true,true]) ++ (rep [true] (n)),([true,true]) ++ (rep [true,true,true] (n)) ++ ([false,true,true,false])⟩ = some ⟨0,([true]) ++ (rep [true,true,true] (n)) ++ ([false,false,true,true]) ++ (rep [true] (n)),([true,true,false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [true] [true,true] [true,true,true] [true,true,true] 3 local3 n (([false,false,true,true]) ++ (rep [true] (n))) (([false,true,true,false]))

theorem phase4 (n : Nat) : run0 table 7 ⟨0,([true]) ++ (rep [true,true,true] (n)) ++ ([false,false,true,true]) ++ (rep [true] (n)),([true,true,false,true,true,false])⟩ = some ⟨1,([false,true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false,false,true,true]) ++ (rep [true] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false,false,true,true]) ++ (rep [true] (n)) = ([false,true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false,false,true,true]) ++ (rep [true] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (28+6*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 13+3*n+8+3*n+7=28+6*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 23 (fun n => 28+6*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2288

namespace M2473

-- 1RB1RB_1RC1RF_0RD---_1LD0RA_0LB1LE_0LE1RA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false,false,true]) ++ (rep [true] (n)),[]⟩

theorem entry : run0 table 23 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 13 ⟨1,([false,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false,false,true]) ++ (rep [true] (n)),[]⟩ = some ⟨4,([true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false,false,true]) ++ (rep [true] (n)),([false,true,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨4,([true,true,true,true]) ++ ([true,true,true]) ++ (L),(R)⟩ = some ⟨4,([true,true,true,true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨4,([true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false,false,true]) ++ (rep [true] (n)),([false,true,true,false])⟩ = some ⟨4,([true,true,true,true,false,false,true]) ++ (rep [true] (n)),(rep [true,true,true] (n)) ++ ([false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,true,true,true] [] [true,true,true] [true,true,true] 3 local1 n (([false,false,true]) ++ (rep [true] (n))) (([false,true,true,false]))

theorem phase2 (n : Nat) : run0 table 8 ⟨4,([true,true,true,true,false,false,true]) ++ (rep [true] (n)),(rep [true,true,true] (n)) ++ ([false,true,true,false])⟩ = some ⟨0,([true,false,false,true,true]) ++ (rep [true] (n)),([true,true]) ++ (rep [true,true,true] (n)) ++ ([false,true,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨0,([true]) ++ (L),([true,true]) ++ ([true,true,true]) ++ (R)⟩ = some ⟨0,([true]) ++ ([true,true,true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨0,([true,false,false,true,true]) ++ (rep [true] (n)),([true,true]) ++ (rep [true,true,true] (n)) ++ ([false,true,true,false])⟩ = some ⟨0,([true]) ++ (rep [true,true,true] (n)) ++ ([false,false,true,true]) ++ (rep [true] (n)),([true,true,false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [true] [true,true] [true,true,true] [true,true,true] 3 local3 n (([false,false,true,true]) ++ (rep [true] (n))) (([false,true,true,false]))

theorem phase4 (n : Nat) : run0 table 7 ⟨0,([true]) ++ (rep [true,true,true] (n)) ++ ([false,false,true,true]) ++ (rep [true] (n)),([true,true,false,true,true,false])⟩ = some ⟨1,([false,true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false,false,true,true]) ++ (rep [true] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false,false,true,true]) ++ (rep [true] (n)) = ([false,true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false,false,true,true]) ++ (rep [true] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (28+6*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 13+3*n+8+3*n+7=28+6*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 23 (fun n => 28+6*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2473

end BB6.Agent11Raw39Pumps
