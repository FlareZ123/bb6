import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B1RCPumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M176

-- 1RB1RC_1RC0RF_0RD0LE_1LD0RA_1LC1RE_1RE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
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

def family (n : Nat) : Z0 := ⟨4,([false,true,true]) ++ (rep [true] (n)) ++ ([false,true,false,false]),[]⟩

theorem entry : run0 table 20 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 3 ⟨4,([false,true,true]) ++ ([true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (3*n) ⟨4,([false,true,true]) ++ (rep [true] (n)) ++ ([false,true,false,false]),[]⟩ = some ⟨4,([false,true,true,false,true,false,false]),(rep [true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true] [] [true] [true] 3 local0 n (([false,true,false,false])) ([])

theorem phase1 (n : Nat) : run0 table 13 ⟨4,([false,true,true,false,true,false,false]),(rep [true] (n))⟩ = some ⟨4,([true,true,false,true,false,false]),([true]) ++ (rep [true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 1 ⟨4,([true]) ++ (L),([true]) ++ ([true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (1*n) ⟨4,([true,true,false,true,false,false]),([true]) ++ (rep [true] (n))⟩ = some ⟨4,([true]) ++ (rep [true] (n)) ++ ([true,false,true,false,false]),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true] [true] [true] 1 local2 n (([true,false,true,false,false])) ([])

theorem phase3 (n : Nat) : run0 table 2 ⟨4,([true]) ++ (rep [true] (n)) ++ ([true,false,true,false,false]),([true])⟩ = some ⟨4,([false,true,true]) ++ (rep [true] (n)) ++ ([true,false,true,false,false]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true]) ++ (rep [true] (n)) ++ ([true,false,true,false,false]) = ([false,true,true,true]) ++ (rep [true] (n)) ++ ([false,true,false,false]) := by
  calc
    _ = ([false,true,true,true]) ++ (rep [true] (n)) ++ ([false,true,false,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true])) (([false,true,false,false])) [] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (15+4*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 3*n+13+1*n+2=15+4*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 20 (fun n => 15+4*n) entry (by intro n; omega) growth m hm

#print axioms never

end M176

namespace M199

-- 1RB1RC_1RC---_0RD0LE_1LD0RA_1LF1RF_1LC0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n))⟩

theorem entry : run0 table 23 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨5,[],([true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n))⟩ = some ⟨3,([true,false]),([true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨3,([true]) ++ (L),([true,false,true,true,false,true]) ++ ([true,false,true,true,false,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,false,false,true,false]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨3,([true,false]),([true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true,false,true,true,false,true] [true,false,true,true,false,true] [false,true,false,false,true,false] 6 local1 n (([false])) ([])

theorem phase2 (n : Nat) : run0 table 14 ⟨3,([true]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true])⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 22 ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ ([false,true,false,false,true,false]) ++ (L),(R)⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (22*n) ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([false]),[]⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false]),(rep [true,false,true,true,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 2 [true,true,false,true,false,false,true,false,false,true,false] [] [false,true,false,false,true,false] [true,false,true,true,false,true] 22 local3 n (([false])) ([])

theorem phase4 (n : Nat) : run0 table 38 ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false]),(rep [true,false,true,true,false,true] (n))⟩ = some ⟨5,[],([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) = ([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (54+28*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 2+6*n+14+22*n+38=54+28*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 23 (fun n => 54+28*n) entry (by intro n; omega) growth m hm

#print axioms never

end M199

namespace M200

-- 1RB1RC_1RC---_0RD0LE_1LD0RA_1LF1RF_1LC1LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n))⟩

theorem entry : run0 table 19 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨5,[],([true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n))⟩ = some ⟨3,([true,false]),([true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨3,([true]) ++ (L),([true,false,true,true,false,true]) ++ ([true,false,true,true,false,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,false,false,true,false]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨3,([true,false]),([true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true,false,true,true,false,true] [true,false,true,true,false,true] [false,true,false,false,true,false] 6 local1 n (([false])) ([])

theorem phase2 (n : Nat) : run0 table 14 ⟨3,([true]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true])⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 14 ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ ([false,true,false,false,true,false]) ++ (L),(R)⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (14*n) ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([false]),[]⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false]),(rep [true,false,true,true,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 2 [true,true,false,true,false,false,true,false,false,true,false] [] [false,true,false,false,true,false] [true,false,true,true,false,true] 14 local3 n (([false])) ([])

theorem phase4 (n : Nat) : run0 table 26 ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false]),(rep [true,false,true,true,false,true] (n))⟩ = some ⟨5,[],([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) = ([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (42+20*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 2+6*n+14+14*n+26=42+20*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 19 (fun n => 42+20*n) entry (by intro n; omega) growth m hm

#print axioms never

end M200

namespace M215

-- 1RB1RC_1RC0LB_0RD0LF_1LD0RA_1LC---_1LA0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 10 ⟨1,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨3,([true]) ++ (L),([false,false,false,true,false,false]) ++ ([false,true,false,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,false]) ++ (L),([false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,false,false,true,false,false] [false,true,false,false] [false,true,true,false] 4 local1 n (([false])) ([])

theorem phase2 (n : Nat) : run0 table 8 ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 28 ⟨3,([false,false,true,true,false,false,true,true,false]) ++ ([false,true,true,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (L),([false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (28*n) ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true,false,false,true,true,false] [] [false,true,true,false] [false,true,false,false] 28 local3 n (([false])) ([])

theorem phase4 (n : Nat) : run0 table 40 ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ = some ⟨1,[],([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) = ([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (58+32*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 10+4*n+8+28*n+40=58+32*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 15 (fun n => 58+32*n) entry (by intro n; omega) growth m hm

#print axioms never

end M215

namespace M216

-- 1RB1RC_1RC---_0RD0LF_1LD0RA_1LC0LE_1LB0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨4,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨3,([true]) ++ (L),([false,false,false,true,false,false]) ++ ([false,true,false,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,false]) ++ (L),([false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,false,false,true,false,false] [false,true,false,false] [false,true,true,false] 4 local1 n (([false])) ([])

theorem phase2 (n : Nat) : run0 table 8 ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 20 ⟨3,([false,false,true,true,false,false,true,true,false]) ++ ([false,true,true,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (L),([false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (20*n) ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true,false,false,true,true,false] [] [false,true,true,false] [false,true,false,false] 20 local3 n (([false])) ([])

theorem phase4 (n : Nat) : run0 table 32 ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ = some ⟨4,[],([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) = ([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (42+24*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 2+4*n+8+20*n+32=42+24*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 15 (fun n => 42+24*n) entry (by intro n; omega) growth m hm

#print axioms never

end M216

namespace M217

-- 1RB1RC_1RC---_0RD0LF_1LD0RA_1LC0LF_1LB0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨4,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨3,([true]) ++ (L),([false,false,false,true,false,false]) ++ ([false,true,false,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,false]) ++ (L),([false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,false,false,true,false,false] [false,true,false,false] [false,true,true,false] 4 local1 n (([false])) ([])

theorem phase2 (n : Nat) : run0 table 8 ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 20 ⟨3,([false,false,true,true,false,false,true,true,false]) ++ ([false,true,true,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (L),([false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (20*n) ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true,false,false,true,true,false] [] [false,true,true,false] [false,true,false,false] 20 local3 n (([false])) ([])

theorem phase4 (n : Nat) : run0 table 32 ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ = some ⟨4,[],([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) = ([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (42+24*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 2+4*n+8+20*n+32=42+24*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 15 (fun n => 42+24*n) entry (by intro n; omega) growth m hm

#print axioms never

end M217

namespace M218

-- 1RB1RC_1RC---_0RD0LF_1LD0RA_1LC0RF_1LB0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨4,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨3,([true]) ++ (L),([false,false,false,true,false,false]) ++ ([false,true,false,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,false]) ++ (L),([false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,false,false,true,false,false] [false,true,false,false] [false,true,true,false] 4 local1 n (([false])) ([])

theorem phase2 (n : Nat) : run0 table 8 ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 28 ⟨3,([false,false,true,true,false,false,true,true,false]) ++ ([false,true,true,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (L),([false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (28*n) ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true,false,false,true,true,false] [] [false,true,true,false] [false,true,false,false] 28 local3 n (([false])) ([])

theorem phase4 (n : Nat) : run0 table 40 ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ = some ⟨4,[],([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) = ([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (50+32*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 2+4*n+8+28*n+40=50+32*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 15 (fun n => 50+32*n) entry (by intro n; omega) growth m hm

#print axioms never

end M218

namespace M219

-- 1RB1RC_1RC---_0RD0LF_1LD0RA_1LC1LA_1LB0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨true,false,0⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨4,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨3,([true]) ++ (L),([false,false,false,true,false,false]) ++ ([false,true,false,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,false]) ++ (L),([false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,false,false,true,false,false] [false,true,false,false] [false,true,true,false] 4 local1 n (([false])) ([])

theorem phase2 (n : Nat) : run0 table 8 ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 22 ⟨3,([false,false,true,true,false,false,true,true,false]) ++ ([false,true,true,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (L),([false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (22*n) ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true,false,false,true,true,false] [] [false,true,true,false] [false,true,false,false] 22 local3 n (([false])) ([])

theorem phase4 (n : Nat) : run0 table 34 ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ = some ⟨4,[],([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) = ([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (44+26*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 2+4*n+8+22*n+34=44+26*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 15 (fun n => 44+26*n) entry (by intro n; omega) growth m hm

#print axioms never

end M219

namespace M220

-- 1RB1RC_1RC---_0RD0LF_1LD0RA_1LC1LC_1LB0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨true,false,2⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨4,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨3,([true]) ++ (L),([false,false,false,true,false,false]) ++ ([false,true,false,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,false]) ++ (L),([false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,false,false,true,false,false] [false,true,false,false] [false,true,true,false] 4 local1 n (([false])) ([])

theorem phase2 (n : Nat) : run0 table 15 ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ = some ⟨2,([true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([true,false,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨2,([true,false,false,true,true,false]) ++ ([false,true,true,false]) ++ (L),(R)⟩ = some ⟨2,([true,false,false,true,true,false]) ++ (L),([true,false,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨2,([true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([true,false,false])⟩ = some ⟨2,([true,false,false,true,true,false,false]),(rep [true,false,false,false] (n)) ++ ([true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 2 [true,false,false,true,true,false] [] [false,true,true,false] [true,false,false,false] 6 local3 n (([false])) (([true,false,false]))

theorem phase4 (n : Nat) : run0 table 11 ⟨2,([true,false,false,true,true,false,false]),(rep [true,false,false,false] (n)) ++ ([true,false,false])⟩ = some ⟨4,[],([false,false,false,true,false,false,false]) ++ (rep [true,false,false,false] (n)) ++ ([true,false,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,false,true,false,false,false]) ++ (rep [true,false,false,false] (n)) ++ ([true,false,false]) = ([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) := by
  calc
    _ = ([false,false,false,true,false,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([false,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,true,false,false,false])) (([false,false])) [false,false,false] true n
    _ = ([false,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false] (n)) ++ ([false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,true,false,false,false,true])) (([false])) [false,false,true] false n
    _ = ([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,true,false,false,false,true,false])) ([]) [false,true,false] false n

theorem growth (n : Nat) : run0 table (28+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 2+4*n+15+6*n+11=28+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 15 (fun n => 28+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M220

namespace M221

-- 1RB1RC_1RC---_0RD0LF_1LD0RA_1LC1LE_1LB0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨4,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨3,([true]) ++ (L),([false,false,false,true,false,false]) ++ ([false,true,false,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,false]) ++ (L),([false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,false,false,true,false,false] [false,true,false,false] [false,true,true,false] 4 local1 n (([false])) ([])

theorem phase2 (n : Nat) : run0 table 8 ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 26 ⟨3,([false,false,true,true,false,false,true,true,false]) ++ ([false,true,true,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (L),([false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (26*n) ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true,false,false,true,true,false] [] [false,true,true,false] [false,true,false,false] 26 local3 n (([false])) ([])

theorem phase4 (n : Nat) : run0 table 38 ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ = some ⟨4,[],([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) = ([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (48+30*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 2+4*n+8+26*n+38=48+30*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 15 (fun n => 48+30*n) entry (by intro n; omega) growth m hm

#print axioms never

end M221

end BB6.Agent11Raw39B1RCPumps
