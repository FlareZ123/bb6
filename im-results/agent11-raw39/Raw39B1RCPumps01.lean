import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B1RCPumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M47

-- 1RB1RC_1RC---_0RD0LE_1LD0RA_1LB0LF_1LC0RE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨false,true,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨5,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨3,([true]) ++ (L),([false,false,false,true,false,false]) ++ ([false,true,false,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,false]) ++ (L),([false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,false,false,true,false,false] [false,true,false,false] [false,true,true,false] 4 local1 n (([false])) ([])

theorem phase2 (n : Nat) : run0 table 8 ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 28 ⟨3,([false,false,true,true,false,false,true,true,false]) ++ ([false,true,true,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (L),([false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (28*n) ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true,false,false,true,true,false] [] [false,true,true,false] [false,true,false,false] 28 local3 n (([false])) ([])

theorem phase4 (n : Nat) : run0 table 40 ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ = some ⟨5,[],([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

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

end M47

namespace M48

-- 1RB1RC_1RC---_0RD0LE_1LD0RA_1LB0LF_1LC1LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨5,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨3,([true]) ++ (L),([false,false,false,true,false,false]) ++ ([false,true,false,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,false]) ++ (L),([false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,false,false,true,false,false] [false,true,false,false] [false,true,true,false] 4 local1 n (([false])) ([])

theorem phase2 (n : Nat) : run0 table 8 ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 22 ⟨3,([false,false,true,true,false,false,true,true,false]) ++ ([false,true,true,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (L),([false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (22*n) ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true,false,false,true,true,false] [] [false,true,true,false] [false,true,false,false] 22 local3 n (([false])) ([])

theorem phase4 (n : Nat) : run0 table 34 ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ = some ⟨5,[],([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

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

end M48

namespace M49

-- 1RB1RC_1RC---_0RD0LE_1LD0RA_1LB0LF_1LC1LC

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨true,false,2⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨5,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨3,([true]) ++ (L),([false,false,false,true,false,false]) ++ ([false,true,false,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,false]) ++ (L),([false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,false,false,true,false,false] [false,true,false,false] [false,true,true,false] 4 local1 n (([false])) ([])

theorem phase2 (n : Nat) : run0 table 15 ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ = some ⟨2,([true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([true,false,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨2,([true,false,false,true,true,false]) ++ ([false,true,true,false]) ++ (L),(R)⟩ = some ⟨2,([true,false,false,true,true,false]) ++ (L),([true,false,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨2,([true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([true,false,false])⟩ = some ⟨2,([true,false,false,true,true,false,false]),(rep [true,false,false,false] (n)) ++ ([true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 2 [true,false,false,true,true,false] [] [false,true,true,false] [true,false,false,false] 6 local3 n (([false])) (([true,false,false]))

theorem phase4 (n : Nat) : run0 table 11 ⟨2,([true,false,false,true,true,false,false]),(rep [true,false,false,false] (n)) ++ ([true,false,false])⟩ = some ⟨5,[],([false,false,false,true,false,false,false]) ++ (rep [true,false,false,false] (n)) ++ ([true,false,false])⟩ := by rfl

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

end M49

namespace M50

-- 1RB1RC_1RC---_0RD0LE_1LD0RA_1LB0LF_1LC1LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨5,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨3,([true]) ++ (L),([false,false,false,true,false,false]) ++ ([false,true,false,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,false]) ++ (L),([false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,false,false,true,false,false] [false,true,false,false] [false,true,true,false] 4 local1 n (([false])) ([])

theorem phase2 (n : Nat) : run0 table 8 ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 26 ⟨3,([false,false,true,true,false,false,true,true,false]) ++ ([false,true,true,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (L),([false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (26*n) ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true,false,false,true,true,false] [] [false,true,true,false] [false,true,false,false] 26 local3 n (([false])) ([])

theorem phase4 (n : Nat) : run0 table 38 ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ = some ⟨5,[],([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

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

end M50

namespace M51

-- 1RB1RC_1RC---_0RD0LE_1LD0RA_1LB0LF_1LC1RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨5,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨3,([true]) ++ (L),([false,false,false,true,false,false]) ++ ([false,true,false,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,false]) ++ (L),([false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,false,false,true,false,false] [false,true,false,false] [false,true,true,false] 4 local1 n (([false])) ([])

theorem phase2 (n : Nat) : run0 table 8 ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 34 ⟨3,([false,false,true,true,false,false,true,true,false]) ++ ([false,true,true,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (L),([false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (34*n) ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true,false,false,true,true,false] [] [false,true,true,false] [false,true,false,false] 34 local3 n (([false])) ([])

theorem phase4 (n : Nat) : run0 table 46 ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ = some ⟨5,[],([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) = ([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (56+38*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 2+4*n+8+34*n+46=56+38*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 15 (fun n => 56+38*n) entry (by intro n; omega) growth m hm

#print axioms never

end M51

namespace M52

-- 1RB1RC_1RC---_0RD0LE_1LD0RA_1LB0LF_1LC1RC

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨true,true,2⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨5,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨3,([true]) ++ (L),([false,false,false,true,false,false]) ++ ([false,true,false,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,false]) ++ (L),([false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,false,false,true,false,false] [false,true,false,false] [false,true,true,false] 4 local1 n (([false])) ([])

theorem phase2 (n : Nat) : run0 table 8 ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 14 ⟨3,([false,false,true,true,false,false,true,true,false]) ++ ([false,true,true,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (L),([false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (14*n) ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true,false,false,true,true,false] [] [false,true,true,false] [false,true,false,false] 14 local3 n (([false])) ([])

theorem phase4 (n : Nat) : run0 table 26 ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ = some ⟨5,[],([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) = ([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (36+18*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 2+4*n+8+14*n+26=36+18*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 15 (fun n => 36+18*n) entry (by intro n; omega) growth m hm

#print axioms never

end M52

namespace M53

-- 1RB1RC_1RC---_0RD0LE_1LD0RA_1LB0LF_1LC1RF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨true,true,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨5,[],([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨3,([true]) ++ (L),([false,false,false,true,false,false]) ++ ([false,true,false,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,false]) ++ (L),([false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,false,false,true,false,false] [false,true,false,false] [false,true,true,false] 4 local1 n (([false])) ([])

theorem phase2 (n : Nat) : run0 table 14 ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ = some ⟨5,([false,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 18 ⟨5,([false,true,false,false,true,true,false]) ++ ([false,true,true,false]) ++ (L),(R)⟩ = some ⟨5,([false,true,false,false,true,true,false]) ++ (L),([false,false,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (18*n) ⟨5,([false,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false])⟩ = some ⟨5,([false,true,false,false,true,true,false,false]),(rep [false,false,false,true] (n)) ++ ([false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true,false,false,true,true,false] [] [false,true,true,false] [false,false,false,true] 18 local3 n (([false])) (([false,false]))

theorem phase4 (n : Nat) : run0 table 24 ⟨5,([false,true,false,false,true,true,false,false]),(rep [false,false,false,true] (n)) ++ ([false,false])⟩ = some ⟨5,[],([false,false,false,true,false,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([false,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,false,true,false,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([false,false]) = ([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) := by
  calc
    _ = ([false,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false] (n)) ++ ([false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,true,false,false,false,true])) (([false])) [false,false,true] false n
    _ = ([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,true,false,false,false,true,false])) ([]) [false,true,false] false n

theorem growth (n : Nat) : run0 table (40+22*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 2+4*n+14+18*n+24=40+22*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 15 (fun n => 40+22*n) entry (by intro n; omega) growth m hm

#print axioms never

end M53

namespace M56

-- 1RB1RC_1RC0LE_0RD0LE_1LD0RA_0LB0LF_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false])⟩

theorem entry : run0 table 12 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨4,[],([true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false])⟩ = some ⟨2,([false,true]),([true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 8 ⟨2,([false]) ++ (L),([true,false]) ++ ([false,false,true,false,false,false,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (8*n) ⟨2,([false,true]),([true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false] [false,false,true,false,false,false,true,false] [true,true,false,false,true,true,false,false] 8 local1 n (([true])) (([true,false,false]))

theorem phase2 (n : Nat) : run0 table 3 ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,true,false,false])⟩ = some ⟨1,([true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([false,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 8 ⟨1,([true,true,false,false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,false]) ++ (L),([false,true,false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (8*n) ⟨1,([true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([false,false])⟩ = some ⟨1,([true,true,false,false,true]),(rep [false,true,false,false,false,true,false,false] (n)) ++ ([false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,false] [] [true,true,false,false,true,true,false,false] [false,true,false,false,false,true,false,false] 8 local3 n (([true])) (([false,false]))

theorem phase4 (n : Nat) : run0 table 17 ⟨1,([true,true,false,false,true]),(rep [false,true,false,false,false,true,false,false] (n)) ++ ([false,false])⟩ = some ⟨2,([false,true]),([true,false,false,false,true,false,false]) ++ (rep [false,true,false,false,false,true,false,false] (n)) ++ ([false,false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 8 ⟨2,([false]) ++ (L),([true,false,false,false,true,false,false]) ++ ([false,true,false,false,false,true,false,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),([true,false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (8*n) ⟨2,([false,true]),([true,false,false,false,true,false,false]) ++ (rep [false,true,false,false,false,true,false,false] (n)) ++ ([false,false])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,false,true,false,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,false,true,false,false] [false,true,false,false,false,true,false,false] [true,true,false,false,true,true,false,false] 8 local5 n (([true])) (([false,false]))

theorem phase6 (n : Nat) : run0 table 16 ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,false,true,false,false,false,false])⟩ = some ⟨4,([true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 8 ⟨4,([true,false,false,true,true,false,false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),(R)⟩ = some ⟨4,([true,false,false,true,true,false,false]) ++ (L),([false,false,true,false,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (8*n) ⟨4,([true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false])⟩ = some ⟨4,([true,false,false,true,true,false,false,true]),(rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,false,true,true,false,false] [] [true,true,false,false,true,true,false,false] [false,false,true,false,false,false,true,false] 8 local7 n (([true])) (([true,false,false]))

theorem phase8 (n : Nat) : run0 table 18 ⟨4,([true,false,false,true,true,false,false,true]),(rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false])⟩ = some ⟨4,[],([true,false,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false]) = ([true,false,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false]) := by
  rfl

theorem growth (n : Nat) : run0 table (56+32*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 2+8*n+3+8*n+17+8*n+16+8*n+18=56+32*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 12 (fun n => 56+32*n) entry (by intro n; omega) growth m hm

#print axioms never

end M56

namespace M58

-- 1RB1RC_1RC1LA_0RD0LE_1LD0RA_0LB0LF_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false])⟩

theorem entry : run0 table 11 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 3 ⟨5,[],([false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false])⟩ = some ⟨2,([false,true]),([true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 8 ⟨2,([false]) ++ (L),([true,false]) ++ ([false,false,true,false,false,false,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (8*n) ⟨2,([false,true]),([true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false] [false,false,true,false,false,false,true,false] [true,true,false,false,true,true,false,false] 8 local1 n (([true])) (([true,false,false]))

theorem phase2 (n : Nat) : run0 table 3 ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,true,false,false])⟩ = some ⟨1,([true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([false,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 12 ⟨1,([true,true,false,false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,false]) ++ (L),([false,true,false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (12*n) ⟨1,([true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([false,false])⟩ = some ⟨1,([true,true,false,false,true]),(rep [false,true,false,false,false,true,false,false] (n)) ++ ([false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,false] [] [true,true,false,false,true,true,false,false] [false,true,false,false,false,true,false,false] 12 local3 n (([true])) (([false,false]))

theorem phase4 (n : Nat) : run0 table 15 ⟨1,([true,true,false,false,true]),(rep [false,true,false,false,false,true,false,false] (n)) ++ ([false,false])⟩ = some ⟨2,([false,true]),([true,false,false,false,true,false,false]) ++ (rep [false,true,false,false,false,true,false,false] (n)) ++ ([false,false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 8 ⟨2,([false]) ++ (L),([true,false,false,false,true,false,false]) ++ ([false,true,false,false,false,true,false,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),([true,false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (8*n) ⟨2,([false,true]),([true,false,false,false,true,false,false]) ++ (rep [false,true,false,false,false,true,false,false] (n)) ++ ([false,false])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,false,true,false,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,false,true,false,false] [false,true,false,false,false,true,false,false] [true,true,false,false,true,true,false,false] 8 local5 n (([true])) (([false,false]))

theorem phase6 (n : Nat) : run0 table 16 ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,false,true,false,false,false,false])⟩ = some ⟨4,([true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 12 ⟨4,([true,false,false,true,true,false,false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),(R)⟩ = some ⟨4,([true,false,false,true,true,false,false]) ++ (L),([false,false,true,false,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (12*n) ⟨4,([true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false])⟩ = some ⟨4,([true,false,false,true,true,false,false,true]),(rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,false,true,true,false,false] [] [true,true,false,false,true,true,false,false] [false,false,true,false,false,false,true,false] 12 local7 n (([true])) (([true,false,false]))

theorem phase8 (n : Nat) : run0 table 15 ⟨4,([true,false,false,true,true,false,false,true]),(rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false])⟩ = some ⟨5,[],([false,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false]) = ([false,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([true,false,false]) := by
  rfl

theorem growth (n : Nat) : run0 table (52+40*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 3+8*n+3+12*n+15+8*n+16+12*n+15=52+40*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 11 (fun n => 52+40*n) entry (by intro n; omega) growth m hm

#print axioms never

end M58

namespace M70

-- 1RB1RC_1RC0LC_0RD0LE_1LD0RA_1LC0LF_1RE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,[],([true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩

theorem entry : run0 table 17 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨2,[],([true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩ = some ⟨3,([true,false]),([false,true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 10 ⟨3,([true,false]) ++ (L),([false,true,false,true,false]) ++ ([true,false,true,false]) ++ (R)⟩ = some ⟨3,([true,false]) ++ ([true,true,false,false]) ++ (L),([false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (10*n) ⟨3,([true,false]),([false,true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩ = some ⟨3,([true,false]) ++ (rep [true,true,false,false] (n)),([false,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true,false] [false,true,false,true,false] [true,false,true,false] [true,true,false,false] 10 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 21 ⟨3,([true,false]) ++ (rep [true,true,false,false] (n)),([false,true,false,true,false])⟩ = some ⟨4,([false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)),([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨4,([false,true,true,false,false,true,true,false,false]) ++ ([true,true,false,false]) ++ (L),(R)⟩ = some ⟨4,([false,true,true,false,false,true,true,false,false]) ++ (L),([false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨4,([false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)),([false])⟩ = some ⟨4,([false,true,true,false,false,true,true,false,false]),(rep [false,true,false,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true,false,false,true,true,false,false] [] [true,true,false,false] [false,true,false,true] 6 local3 n ([]) (([false]))

theorem phase4 (n : Nat) : run0 table 13 ⟨4,([false,true,true,false,false,true,true,false,false]),(rep [false,true,false,true] (n)) ++ ([false])⟩ = some ⟨2,[],([true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([false]) = ([true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) := by
  calc
    _ = ([true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,false,true,false,true,false,true])) ([]) [true,false,true] false n

theorem growth (n : Nat) : run0 table (35+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 1+10*n+21+6*n+13=35+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 17 (fun n => 35+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M70

end BB6.Agent11Raw39B1RCPumps
