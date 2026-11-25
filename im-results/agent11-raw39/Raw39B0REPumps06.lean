import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B0REPumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M2689

-- 1RB0RE_1RC0LF_0RD1LB_1LD0RA_---1RF_1LC0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,[],([true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n))⟩

theorem entry : run0 table 19 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨2,[],([true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n))⟩ = some ⟨3,([true,false]),([false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 14 ⟨3,([true]) ++ (L),([false,true,true,false,true,true]) ++ ([false,true,true,false,true,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,false,true,true]) ++ (L),([false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (14*n) ⟨3,([true,false]),([false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false]),([false,true,true,false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,true,true,false,true,true] [false,true,true,false,true,true] [false,true,true,false,true,true] 14 local1 n (([false])) ([])

theorem phase2 (n : Nat) : run0 table 31 ⟨3,([true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false]),([false,true,true,false,true,true])⟩ = some ⟨2,([true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false]),([true,false,true,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨2,([true,true,false,true,true,false,true,true]) ++ ([false,true,true,false,true,true]) ++ (L),(R)⟩ = some ⟨2,([true,true,false,true,true,false,true,true]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨2,([true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false]),([true,false,true,true])⟩ = some ⟨2,([true,true,false,true,true,false,true,true,false]),(rep [true,false,true,true,false,true] (n)) ++ ([true,false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 2 [true,true,false,true,true,false,true,true] [] [false,true,true,false,true,true] [true,false,true,true,false,true] 6 local3 n (([false])) (([true,false,true,true]))

theorem phase4 (n : Nat) : run0 table 9 ⟨2,([true,true,false,true,true,false,true,true,false]),(rep [true,false,true,true,false,true] (n)) ++ ([true,false,true,true])⟩ = some ⟨2,[],([true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true,false,true,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true,false,true,true]) = ([true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) := by
  calc
    _ = ([true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,true,false,true,true,false,true])) (([false,true,true])) [false,true,true,false,true] true n
    _ = ([true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,true,false,true,true,false,true,true])) (([true,true])) [true,true,false,true,true] false n
    _ = ([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,true,false,true,true,false,true,true,false])) (([true])) [true,false,true,true,false] true n
    _ = ([true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,true,false,true,true,false,true,true,false,true])) ([]) [false,true,true,false,true] true n

theorem growth (n : Nat) : run0 table (41+20*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 1+14*n+31+6*n+9=41+20*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 19 (fun n => 41+20*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2689

namespace M2690

-- 1RB0RE_1RC0LF_0RD1LB_1LD0RA_---1RF_1LC1RC

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨true,true,2⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,[],([true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n))⟩

theorem entry : run0 table 19 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨2,[],([true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n))⟩ = some ⟨3,([true,false]),([false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 10 ⟨3,([true]) ++ (L),([false,true,true,false,true,true]) ++ ([false,true,true,false,true,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,false,false,true,false]) ++ (L),([false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (10*n) ⟨3,([true,false]),([false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([false]),([false,true,true,false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,true,true,false,true,true] [false,true,true,false,true,true] [false,true,false,false,true,false] 10 local1 n (([false])) ([])

theorem phase2 (n : Nat) : run0 table 19 ⟨3,([true]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([false]),([false,true,true,false,true,true])⟩ = some ⟨5,([false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 10 ⟨5,([false,true,false,false,true,false,false,true,false,false,true,false]) ++ ([false,true,false,false,true,false]) ++ (L),(R)⟩ = some ⟨5,([false,true,false,false,true,false,false,true,false,false,true,false]) ++ (L),([false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (10*n) ⟨5,([false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([false]),[]⟩ = some ⟨5,([false,true,false,false,true,false,false,true,false,false,true,false,false]),(rep [false,true,true,false,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true,false,false,true,false,false,true,false,false,true,false] [] [false,true,false,false,true,false] [false,true,true,false,true,true] 10 local3 n (([false])) ([])

theorem phase4 (n : Nat) : run0 table 21 ⟨5,([false,true,false,false,true,false,false,true,false,false,true,false,false]),(rep [false,true,true,false,true,true] (n))⟩ = some ⟨2,[],([true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) = ([true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (41+20*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 1+10*n+19+10*n+21=41+20*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 19 (fun n => 41+20*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2690

namespace M2735

-- 1RB0RE_1RC1LF_0RD---_1LD0RA_0LB1RF_1LE0LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 10 ⟨2,([false,true,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨5,([false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),([false,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨5,([false,false,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨5,([false,false,true]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨5,([false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),([false,false])⟩ = some ⟨5,([false,false,true]),(rep [true,false,true,true,false,true] (n)) ++ ([false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,true] [] [false,false,true,false,false,true] [true,false,true,true,false,true] 6 local1 n ([]) (([false,false]))

theorem phase2 (n : Nat) : run0 table 6 ⟨5,([false,false,true]),(rep [true,false,true,true,false,true] (n)) ++ ([false,false])⟩ = some ⟨2,([false,true]),([true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([false,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 10 ⟨2,([false]) ++ (L),([true,true,false,true]) ++ ([true,false,true,true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (10*n) ⟨2,([false,true]),([true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([false,false])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true] [true,false,true,true,false,true] [true,false,false,true,false,false] 10 local3 n (([true])) (([false,false]))

theorem phase4 (n : Nat) : run0 table 9 ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,false,false])⟩ = some ⟨2,([false,true,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,false,true,false,false])) ([]) [false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (25+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 10+6*n+6+10*n+9=25+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 25+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2735

namespace M143

-- 1RB0RE_1RC1LB_0RD0RD_1LD0RA_1LE0LF_1LA---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true,false,false,true,true,false,true,true,false,true,true,false,true,true,true,false,false]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true,false,false,true]),[]⟩

theorem entry : run0 table 407 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 390 ⟨1,([false,true,false,false,true,true,false,true,true,false,true,true,false,true,true,true,false,false]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true,false,false,true]),[]⟩ = some ⟨1,([false,true,false,false,true,true,false,true,true,false,true,true,false,true,true,true,false,false,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true,false,false,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,true,false,true,true,false,true,true,false,true,true,true,false,false,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true,false,false,true]) = ([false,true,false,false,true,true,false,true,true,false,true,true,false,true,true,true,false,false,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true,false,false,true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (390+0*n) (family n) = some (family (n+1)) := by
  have H := (phase0 n)
  rw [show 390=390+0*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 407 (fun n => 390+0*n) entry (by intro n; omega) growth m hm

#print axioms never

end M143

end BB6.Agent11Raw39B0REPumps
