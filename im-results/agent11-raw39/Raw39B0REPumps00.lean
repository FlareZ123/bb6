import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B0REPumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M1

-- 1RB0RE_1RC1LF_0RD---_1LD0RA_0LF0LE_1LA0LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([true,false,true,false,false,false]) ++ (rep [true,false,true,false,false,false] (n)) ++ ([false])⟩

theorem entry : run0 table 38 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 13 ⟨5,[],([true,false,true,false,false,false]) ++ (rep [true,false,true,false,false,false] (n)) ++ ([false])⟩ = some ⟨1,([false,true]),([false,true,false,true,false,false,false]) ++ (rep [true,false,true,false,false,false] (n)) ++ ([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 10 ⟨1,([false]) ++ (L),([false,true,false,true,false,false,false]) ++ ([true,false,true,false,false,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,false,false,true,false,true]) ++ (L),([false,true,false,true,false,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (10*n) ⟨1,([false,true]),([false,true,false,true,false,false,false]) ++ (rep [true,false,true,false,false,false] (n)) ++ ([false])⟩ = some ⟨1,([false]) ++ (rep [true,false,false,true,false,true] (n)) ++ ([true]),([false,true,false,true,false,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [false,true,false,true,false,false,false] [true,false,true,false,false,false] [true,false,false,true,false,true] 10 local1 n (([true])) (([false]))

theorem phase2 (n : Nat) : run0 table 19 ⟨1,([false]) ++ (rep [true,false,false,true,false,true] (n)) ++ ([true]),([false,true,false,true,false,false,false,false])⟩ = some ⟨0,([true,false,false,true,false,true]) ++ (rep [true,false,false,true,false,true] (n)) ++ ([true]),([true,false,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 18 ⟨0,([true,false,false,true,false,true]) ++ ([true,false,false,true,false,true]) ++ (L),([true]) ++ (R)⟩ = some ⟨0,([true,false,false,true,false,true]) ++ (L),([true]) ++ ([false,true,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (18*n) ⟨0,([true,false,false,true,false,true]) ++ (rep [true,false,false,true,false,true] (n)) ++ ([true]),([true,false,false])⟩ = some ⟨0,([true,false,false,true,false,true,true]),([true]) ++ (rep [false,true,false,true,false,false] (n)) ++ ([false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,false,false,true,false,true] [true] [true,false,false,true,false,true] [false,true,false,true,false,false] 18 local3 n (([true])) (([false,false]))

theorem phase4 (n : Nat) : run0 table 26 ⟨0,([true,false,false,true,false,true,true]),([true]) ++ (rep [false,true,false,true,false,false] (n)) ++ ([false,false])⟩ = some ⟨2,([false,true]),([true,false,false,false,true,false,true,false,false]) ++ (rep [false,true,false,true,false,false] (n)) ++ ([false,false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 10 ⟨2,([false]) ++ (L),([true,false,false,false,true,false,true,false,false]) ++ ([false,true,false,true,false,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,true,true,false,false]) ++ (L),([true,false,false,false,true,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (10*n) ⟨2,([false,true]),([true,false,false,false,true,false,true,false,false]) ++ (rep [false,true,false,true,false,false] (n)) ++ ([false,false])⟩ = some ⟨2,([false]) ++ (rep [true,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,false,true,false,true,false,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,false,true,false,true,false,false] [false,true,false,true,false,false] [true,false,true,true,false,false] 10 local5 n (([true])) (([false,false]))

theorem phase6 (n : Nat) : run0 table 22 ⟨2,([false]) ++ (rep [true,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,false,true,false,true,false,false,false,false])⟩ = some ⟨0,([true,false,false,true,false,true,true,false,false]) ++ (rep [true,false,true,true,false,false] (n)) ++ ([true]),([true,false,false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 18 ⟨0,([true,false,false,true,false,true,true,false,false]) ++ ([true,false,true,true,false,false]) ++ (L),([true]) ++ (R)⟩ = some ⟨0,([true,false,false,true,false,true,true,false,false]) ++ (L),([true]) ++ ([false,true,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (18*n) ⟨0,([true,false,false,true,false,true,true,false,false]) ++ (rep [true,false,true,true,false,false] (n)) ++ ([true]),([true,false,false])⟩ = some ⟨0,([true,false,false,true,false,true,true,false,false,true]),([true]) ++ (rep [false,true,false,true,false,false] (n)) ++ ([false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,false,false,true,false,true,true,false,false] [true] [true,false,true,true,false,false] [false,true,false,true,false,false] 18 local7 n (([true])) (([false,false]))

theorem phase8 (n : Nat) : run0 table 26 ⟨0,([true,false,false,true,false,true,true,false,false,true]),([true]) ++ (rep [false,true,false,true,false,false] (n)) ++ ([false,false])⟩ = some ⟨5,[],([true,false,true,false,false,false,true,false,true,false,false]) ++ (rep [false,true,false,true,false,false] (n)) ++ ([false,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,false,false,false,true,false,true,false,false]) ++ (rep [false,true,false,true,false,false] (n)) ++ ([false,false]) = ([true,false,true,false,false,false,true,false,true,false,false,false]) ++ (rep [true,false,true,false,false,false] (n)) ++ ([false]) := by
  calc
    _ = ([true,false,true,false,false,false,true,false,true,false,false,false]) ++ (rep [true,false,true,false,false,false] (n)) ++ ([false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,false,false,false,true,false,true,false,false])) (([false])) [true,false,true,false,false] false n

theorem growth (n : Nat) : run0 table (106+56*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalR n] at H
  rw [show 13+10*n+19+18*n+26+10*n+22+18*n+26=106+56*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 38 (fun n => 106+56*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1

namespace M8

-- 1RB0RE_1RC0LE_0RD1LB_1LD0RA_0LF0LE_1LC---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true,true,false,false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)),[]⟩

theorem entry : run0 table 38 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 10 ⟨2,([false,true,true,false,false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)),[]⟩ = some ⟨2,([true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)),([true,false,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨2,([true,true,false,false,true,true,false,false]) ++ ([true,true,false,false]) ++ (L),(R)⟩ = some ⟨2,([true,true,false,false,true,true,false,false]) ++ (L),([true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨2,([true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)),([true,false,false])⟩ = some ⟨2,([true,true,false,false,true,true,false,false]),(rep [true,false,false,true] (n)) ++ ([true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 2 [true,true,false,false,true,true,false,false] [] [true,true,false,false] [true,false,false,true] 4 local1 n ([]) (([true,false,false]))

theorem phase2 (n : Nat) : run0 table 18 ⟨2,([true,true,false,false,true,true,false,false]),(rep [true,false,false,true] (n)) ++ ([true,false,false])⟩ = some ⟨3,([true,false]),([false,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true] (n)) ++ ([true,false,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 18 ⟨3,([true]) ++ (L),([false,false,false,true,true,false,false,true]) ++ ([true,false,false,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,false]) ++ (L),([false,false,false,true,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (18*n) ⟨3,([true,false]),([false,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true] (n)) ++ ([true,false,false])⟩ = some ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,true,false,false,true,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,false,false,true,true,false,false,true] [true,false,false,true] [false,true,true,false] 18 local3 n (([false])) (([true,false,false]))

theorem phase4 (n : Nat) : run0 table 30 ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,true,false,false,true,true,false,false])⟩ = some ⟨2,([false,true,true,false,false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,false,false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]) = ([false,true,true,false,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)) := by
  calc
    _ = ([false,true,true,false,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,false,false,true,true,false,false,true,true,false])) ([]) [true,true,false] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (58+22*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 10+4*n+18+18*n+30=58+22*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 38 (fun n => 58+22*n) entry (by intro n; omega) growth m hm

#print axioms never

end M8

namespace M14

-- 1RB0RE_1RC1LB_0RD1LE_1LD0RA_0LF0LE_1LC---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,[],([true,false,false,true,true]) ++ (rep [false,false,true,true] (n)) ++ ([true,false,false])⟩

theorem entry : run0 table 23 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 10 ⟨2,[],([true,false,false,true,true]) ++ (rep [false,false,true,true] (n)) ++ ([true,false,false])⟩ = some ⟨3,([true,false]),([false,false,false,true,true]) ++ (rep [false,false,true,true] (n)) ++ ([true,false,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 18 ⟨3,([true]) ++ (L),([false,false,false,true,true]) ++ ([false,false,true,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,false]) ++ (L),([false,false,false,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (18*n) ⟨3,([true,false]),([false,false,false,true,true]) ++ (rep [false,false,true,true] (n)) ++ ([true,false,false])⟩ = some ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,true,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,false,false,true,true] [false,false,true,true] [false,true,true,false] 18 local1 n (([false])) (([true,false,false]))

theorem phase2 (n : Nat) : run0 table 22 ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,true,true,false,false])⟩ = some ⟨4,([false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([true,true,false,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 4 ⟨4,([false,false,true,true,false]) ++ ([false,true,true,false]) ++ (L),(R)⟩ = some ⟨4,([false,false,true,true,false]) ++ (L),([false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (4*n) ⟨4,([false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([true,true,false,false])⟩ = some ⟨4,([false,false,true,true,false,false]),(rep [false,true,true,false] (n)) ++ ([true,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,false,true,true,false] [] [false,true,true,false] [false,true,true,false] 4 local3 n (([false])) (([true,true,false,false]))

theorem phase4 (n : Nat) : run0 table 16 ⟨4,([false,false,true,true,false,false]),(rep [false,true,true,false] (n)) ++ ([true,true,false,false])⟩ = some ⟨3,([true,false]),([false,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([true,true,false,false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 18 ⟨3,([true]) ++ (L),([false,false,false,true,true,false]) ++ ([false,true,true,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,false]) ++ (L),([false,false,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (18*n) ⟨3,([true,false]),([false,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([true,true,false,false])⟩ = some ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,true,false,true,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,false,false,true,true,false] [false,true,true,false] [false,true,true,false] 18 local5 n (([false])) (([true,true,false,false]))

theorem phase6 (n : Nat) : run0 table 14 ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,true,false,true,true,false,false])⟩ = some ⟨2,([true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([true,true,false,false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 4 ⟨2,([true,true,false,false,true,true,false]) ++ ([false,true,true,false]) ++ (L),(R)⟩ = some ⟨2,([true,true,false,false,true,true,false]) ++ (L),([true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (4*n) ⟨2,([true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([true,true,false,false])⟩ = some ⟨2,([true,true,false,false,true,true,false,false]),(rep [true,false,false,true] (n)) ++ ([true,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 2 [true,true,false,false,true,true,false] [] [false,true,true,false] [true,false,false,true] 4 local7 n (([false])) (([true,true,false,false]))

theorem phase8 (n : Nat) : run0 table 8 ⟨2,([true,true,false,false,true,true,false,false]),(rep [true,false,false,true] (n)) ++ ([true,true,false,false])⟩ = some ⟨2,[],([true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true] (n)) ++ ([true,true,false,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true] (n)) ++ ([true,true,false,false]) = ([true,false,false,true,true,false,false,true,true]) ++ (rep [false,false,true,true] (n)) ++ ([true,false,false]) := by
  calc
    _ = ([true,false,false,true,true,false,false,true,true]) ++ (rep [false,false,true,true] (n)) ++ ([true,false,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,false,true,true,false,false,true])) (([true,false,false])) [false,false,true] true n

theorem growth (n : Nat) : run0 table (70+44*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalR n] at H
  rw [show 10+18*n+22+4*n+16+18*n+14+4*n+8=70+44*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 23 (fun n => 70+44*n) entry (by intro n; omega) growth m hm

#print axioms never

end M14

namespace M70

-- 1RB0RE_1RC0LE_0RD1LD_1LD0RA_1LF0LE_0LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 28 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 9 ⟨2,([false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)),[]⟩ = some ⟨4,([false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)),([false,false,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 8 ⟨4,([false,false,true,true,false,false,true]) ++ ([true,false,false,true,true,false,false,true]) ++ (L),(R)⟩ = some ⟨4,([false,false,true,true,false,false,true]) ++ (L),([false,false,false,true,false,false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (8*n) ⟨4,([false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)),([false,false,true,false])⟩ = some ⟨4,([false,false,true,true,false,false,true]),(rep [false,false,false,true,false,false,false,true] (n)) ++ ([false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,false,true,true,false,false,true] [] [true,false,false,true,true,false,false,true] [false,false,false,true,false,false,false,true] 8 local1 n ([]) (([false,false,true,false]))

theorem phase2 (n : Nat) : run0 table 10 ⟨4,([false,false,true,true,false,false,true]),(rep [false,false,false,true,false,false,false,true] (n)) ++ ([false,false,true,false])⟩ = some ⟨2,([false,true]),([true,false,false,true,false,false,false,true]) ++ (rep [false,false,false,true,false,false,false,true] (n)) ++ ([false,false,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 20 ⟨2,([false]) ++ (L),([true,false,false,true,false,false,false,true]) ++ ([false,false,false,true,false,false,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),([true,false,false,true,false,false,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (20*n) ⟨2,([false,true]),([true,false,false,true,false,false,false,true]) ++ (rep [false,false,false,true,false,false,false,true] (n)) ++ ([false,false,true,false])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,false,false,false,true,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true,false,false,false,true] [false,false,false,true,false,false,false,true] [true,true,false,false,true,true,false,false] 20 local3 n (([true])) (([false,false,true,false]))

theorem phase4 (n : Nat) : run0 table 23 ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,false,false,false,true,false,false,true,false])⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 8 ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),([false,true,false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (8*n) ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([false])⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true]),(rep [false,true,false,false,false,true,false,false] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,false,true,true,false,false,true,true,false,false] [] [true,true,false,false,true,true,false,false] [false,true,false,false,false,true,false,false] 8 local5 n (([true])) (([false]))

theorem phase6 (n : Nat) : run0 table 16 ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true]),(rep [false,true,false,false,false,true,false,false] (n)) ++ ([false])⟩ = some ⟨2,([false,true]),([true,false,false,true,false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false,false,true,false,false] (n)) ++ ([false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 20 ⟨2,([false]) ++ (L),([true,false,false,true,false,false,false,true,false,false,false,true,false,false]) ++ ([false,true,false,false,false,true,false,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),([true,false,false,true,false,false,false,true,false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (20*n) ⟨2,([false,true]),([true,false,false,true,false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false,false,true,false,false] (n)) ++ ([false])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,false,false,false,true,false,false,false,true,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true,false,false,false,true,false,false,false,true,false,false] [false,true,false,false,false,true,false,false] [true,true,false,false,true,true,false,false] 20 local7 n (([true])) (([false]))

theorem phase8 (n : Nat) : run0 table 34 ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,false,false,false,true,false,false,false,true,false,false,false])⟩ = some ⟨2,([false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]) = ([false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false])) ([]) [true,false,false,true,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (92+56*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalL n] at H
  rw [show 9+8*n+10+20*n+23+8*n+16+20*n+34=92+56*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 28 (fun n => 92+56*n) entry (by intro n; omega) growth m hm

#print axioms never

end M70

namespace M71

-- 1RB0RE_1RC1LE_0RD---_1LD0RA_1LF0LE_0LB1RF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,true,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([false,true,false]) ++ (rep [true,false] (n)) ++ ([false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false])⟩

theorem entry : run0 table 56 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 14 ⟨4,[],([false,true,false]) ++ (rep [true,false] (n)) ++ ([false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false])⟩ = some ⟨2,([false,true]),([true,true,false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨2,([false]) ++ (L),([true,true,false,true,false,true,false]) ++ ([true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false]) ++ (L),([true,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨2,([false,true]),([true,true,false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false])⟩ = some ⟨2,([false]) ++ (rep [true,false] (n)) ++ ([true]),([true,true,false,true,false,true,false,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true,false,true,false] [true,false] [true,false] 6 local1 n (([true])) (([false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false]))

theorem phase2 (n : Nat) : run0 table 33 ⟨2,([false]) ++ (rep [true,false] (n)) ++ ([true]),([true,true,false,true,false,true,false,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false])⟩ = some ⟨4,([true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨4,([true,false,true,false]) ++ ([true,false]) ++ (L),(R)⟩ = some ⟨4,([true,false,true,false]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨4,([true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false])⟩ = some ⟨4,([true,false,true,false,true]),(rep [true,false] (n)) ++ ([false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,true,false] [] [true,false] [true,false] 6 local3 n (([true])) (([false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false]))

theorem phase4 (n : Nat) : run0 table 13 ⟨4,([true,false,true,false,true]),(rep [true,false] (n)) ++ ([false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false])⟩ = some ⟨4,[],([false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false]) = ([false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false,true,false]) := by
  rfl

theorem growth (n : Nat) : run0 table (60+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 14+6*n+33+6*n+13=60+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 56 (fun n => 60+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M71

namespace M81

-- 1RB0RE_1RC1RD_0RD---_1LD0RA_1LF0LE_1LA1RA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false,false,false,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] (n)),[]⟩

theorem entry : run0 table 22 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 24 ⟨4,([false,false,false,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] (n)),[]⟩ = some ⟨4,([false,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] (n)),([true,false,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 55 ⟨4,([false,false,true,true,false,true,true]) ++ ([false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,false,true,true,false,true,true]) ++ (L),([false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (55*n) ⟨4,([false,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] (n)),([true,false,true,false])⟩ = some ⟨4,([false,false,true,true,false,true,true]),(rep [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,false,true,true,false,true,true] [] [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] 55 local1 n ([]) (([true,false,true,false]))

theorem phase2 (n : Nat) : run0 table 25 ⟨4,([false,false,true,true,false,true,true]),(rep [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([true,false,true,false])⟩ = some ⟨1,([true,true]),([true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([true,false,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 15 ⟨1,([true]) ++ (L),([true,false,true,true,false,true,true]) ++ ([false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),([true,false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (15*n) ⟨1,([true,true]),([true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([true,false,true,false])⟩ = some ⟨1,([true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([true,false,true,true,false,true,true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,false,true,true,false,true,true] [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] 15 local3 n (([true])) (([true,false,true,false]))

theorem phase4 (n : Nat) : run0 table 60 ⟨1,([true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([true,false,true,true,false,true,true,true,false,true,false])⟩ = some ⟨4,([false,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([true,true,true,true,false,true,false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 55 ⟨4,([false,false,true,true,false,true,true,false,true]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),(R)⟩ = some ⟨4,([false,false,true,true,false,true,true,false,true]) ++ (L),([false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (55*n) ⟨4,([false,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([true,true,true,true,false,true,false])⟩ = some ⟨4,([false,false,true,true,false,true,true,false,true,true]),(rep [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,false,true,true,false,true,true,false,true] [] [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] 55 local5 n (([true])) (([true,true,true,true,false,true,false]))

theorem phase6 (n : Nat) : run0 table 36 ⟨4,([false,false,true,true,false,true,true,false,true,true]),(rep [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,true,true,false,true,false])⟩ = some ⟨1,([true,true]),([true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,true,true,false,true,false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 15 ⟨1,([true]) ++ (L),([true,false,true,true,false,true,true,false,true,true]) ++ ([false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),([true,false,true,true,false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (15*n) ⟨1,([true,true]),([true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,true,true,false,true,false])⟩ = some ⟨1,([true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([true,false,true,true,false,true,true,false,true,true,true,true,true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,false,true,true,false,true,true,false,true,true] [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] 15 local7 n (([true])) (([true,true,true,true,false,true,false]))

theorem phase8 (n : Nat) : run0 table 11 ⟨1,([true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([true,false,true,true,false,true,true,false,true,true,true,true,true,true,false,true,false])⟩ = some ⟨0,([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([true,true,true,false,true,false])⟩ := by rfl

theorem local9 (L R : List Bool) : run0 table 55 ⟨0,([true,false,true,true,false,true,true,false,true,true,false,true]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),([true]) ++ (R)⟩ = some ⟨0,([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),([true]) ++ ([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase9 (n : Nat) : run0 table (55*n) ⟨0,([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([true,true,true,false,true,false])⟩ = some ⟨0,([true,false,true,true,false,true,true,false,true,true,false,true,true]),([true]) ++ (rep [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] (n)) ++ ([true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,false,true,true,false,true,true,false,true,true,false,true] [true] [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] 55 local9 n (([true])) (([true,true,false,true,false]))

theorem phase10 (n : Nat) : run0 table 49 ⟨0,([true,false,true,true,false,true,true,false,true,true,false,true,true]),([true]) ++ (rep [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] (n)) ++ ([true,true,false,true,false])⟩ = some ⟨1,([true,true]),([true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] (n)) ++ ([true,true,false,true,false])⟩ := by rfl

theorem local11 (L R : List Bool) : run0 table 15 ⟨1,([true]) ++ (L),([true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ ([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),([true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase11 (n : Nat) : run0 table (15*n) ⟨1,([true,true]),([true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] (n)) ++ ([true,true,false,true,false])⟩ = some ⟨1,([true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,false,true,true,false,true,true,false,true,true,false,true,true,false] [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] 15 local11 n (([true])) (([true,true,false,true,false]))

theorem phase12 (n : Nat) : run0 table 22 ⟨1,([true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,false])⟩ = some ⟨4,([false,false,false,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]) = ([false,false,false,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] (n)) := by
  calc
    _ = ([false,false,false,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true])) ([]) [false,true,true,false,true,true,false,true,true,false,true,true,false,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (227+210*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n)) (phase9 n)) (phase10 n)) (phase11 n)) (phase12 n))
  rw [finalL n] at H
  rw [show 24+55*n+25+15*n+60+55*n+36+15*n+11+55*n+49+15*n+22=227+210*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 22 (fun n => 227+210*n) entry (by intro n; omega) growth m hm

#print axioms never

end M81

namespace M112

-- 1RB0RE_1RC1LA_0RD0LD_1LD0RA_1LB0LF_0LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true,true,false,false,true,true,false]) ++ (rep [true,false,false,true,true,false] (n)),[]⟩

theorem entry : run0 table 26 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 4 ⟨2,([false,true,true,false,false,true,true,false]) ++ (rep [true,false,false,true,true,false] (n)),[]⟩ = some ⟨0,([true,false,true,false,false,true,true,false]) ++ (rep [true,false,false,true,true,false] (n)),([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 12 ⟨0,([true,false,true,false,false,true,true,false]) ++ ([true,false,false,true,true,false]) ++ (L),([true]) ++ (R)⟩ = some ⟨0,([true,false,true,false,false,true,true,false]) ++ (L),([true]) ++ ([true,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (12*n) ⟨0,([true,false,true,false,false,true,true,false]) ++ (rep [true,false,false,true,true,false] (n)),([true])⟩ = some ⟨0,([true,false,true,false,false,true,true,false]),([true]) ++ (rep [true,false,false,true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,false,true,false,false,true,true,false] [true] [true,false,false,true,true,false] [true,false,false,true,false,false] 12 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 17 ⟨0,([true,false,true,false,false,true,true,false]),([true]) ++ (rep [true,false,false,true,false,false] (n))⟩ = some ⟨2,([true,true]),([false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 8 ⟨2,([true,true]) ++ (L),([false,false,true,false,false,true,false,false]) ++ ([true,false,false,true,false,false]) ++ (R)⟩ = some ⟨2,([true,true]) ++ ([true,false,false,true,true,false]) ++ (L),([false,false,true,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (8*n) ⟨2,([true,true]),([false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n))⟩ = some ⟨2,([true,true]) ++ (rep [true,false,false,true,true,false] (n)),([false,false,true,false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true,true] [false,false,true,false,false,true,false,false] [true,false,false,true,false,false] [true,false,false,true,true,false] 8 local3 n ([]) ([])

theorem phase4 (n : Nat) : run0 table 26 ⟨2,([true,true]) ++ (rep [true,false,false,true,true,false] (n)),([false,false,true,false,false,true,false,false])⟩ = some ⟨4,([true,false,false,true,true,false]) ++ (rep [true,false,false,true,true,false] (n)),([false,false,true,false,false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 12 ⟨4,([true,false,false,true,true,false]) ++ ([true,false,false,true,true,false]) ++ (L),(R)⟩ = some ⟨4,([true,false,false,true,true,false]) ++ (L),([true,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (12*n) ⟨4,([true,false,false,true,true,false]) ++ (rep [true,false,false,true,true,false] (n)),([false,false,true,false,false])⟩ = some ⟨4,([true,false,false,true,true,false]),(rep [true,false,false,true,false,false] (n)) ++ ([false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,false,true,true,false] [] [true,false,false,true,true,false] [true,false,false,true,false,false] 12 local5 n ([]) (([false,false,true,false,false]))

theorem phase6 (n : Nat) : run0 table 9 ⟨4,([true,false,false,true,true,false]),(rep [true,false,false,true,false,false] (n)) ++ ([false,false,true,false,false])⟩ = some ⟨2,([true,true]),([false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([false,false,true,false,false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 8 ⟨2,([true,true]) ++ (L),([false,false,true,false,false]) ++ ([true,false,false,true,false,false]) ++ (R)⟩ = some ⟨2,([true,true]) ++ ([true,false,false,true,true,false]) ++ (L),([false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (8*n) ⟨2,([true,true]),([false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([false,false,true,false,false])⟩ = some ⟨2,([true,true]) ++ (rep [true,false,false,true,true,false] (n)),([false,false,true,false,false,false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true,true] [false,false,true,false,false] [true,false,false,true,false,false] [true,false,false,true,true,false] 8 local7 n ([]) (([false,false,true,false,false]))

theorem phase8 (n : Nat) : run0 table 12 ⟨2,([true,true]) ++ (rep [true,false,false,true,true,false] (n)),([false,false,true,false,false,false,false,true,false,false])⟩ = some ⟨0,([true,false,true,false,false,true,true,false]) ++ (rep [true,false,false,true,true,false] (n)),([true,true,false,false])⟩ := by rfl

theorem local9 (L R : List Bool) : run0 table 12 ⟨0,([true,false,true,false,false,true,true,false]) ++ ([true,false,false,true,true,false]) ++ (L),([true]) ++ (R)⟩ = some ⟨0,([true,false,true,false,false,true,true,false]) ++ (L),([true]) ++ ([true,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase9 (n : Nat) : run0 table (12*n) ⟨0,([true,false,true,false,false,true,true,false]) ++ (rep [true,false,false,true,true,false] (n)),([true,true,false,false])⟩ = some ⟨0,([true,false,true,false,false,true,true,false]),([true]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,false,true,false,false,true,true,false] [true] [true,false,false,true,true,false] [true,false,false,true,false,false] 12 local9 n ([]) (([true,false,false]))

theorem phase10 (n : Nat) : run0 table 17 ⟨0,([true,false,true,false,false,true,true,false]),([true]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,false,false])⟩ = some ⟨2,([true,true]),([false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,false,false])⟩ := by rfl

theorem local11 (L R : List Bool) : run0 table 8 ⟨2,([true,true]) ++ (L),([false,false,true,false,false,true,false,false]) ++ ([true,false,false,true,false,false]) ++ (R)⟩ = some ⟨2,([true,true]) ++ ([true,false,false,true,true,false]) ++ (L),([false,false,true,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase11 (n : Nat) : run0 table (8*n) ⟨2,([true,true]),([false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,false,false])⟩ = some ⟨2,([true,true]) ++ (rep [true,false,false,true,true,false] (n)),([false,false,true,false,false,true,false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true,true] [false,false,true,false,false,true,false,false] [true,false,false,true,false,false] [true,false,false,true,true,false] 8 local11 n ([]) (([true,false,false]))

theorem phase12 (n : Nat) : run0 table 16 ⟨2,([true,true]) ++ (rep [true,false,false,true,true,false] (n)),([false,false,true,false,false,true,false,false,true,false,false])⟩ = some ⟨2,([false,true,true,false,false,true,true,false,true,false,false,true,true,false]) ++ (rep [true,false,false,true,true,false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,false,false,true,true,false,true,false,false,true,true,false]) ++ (rep [true,false,false,true,true,false] (n)) = ([false,true,true,false,false,true,true,false,true,false,false,true,true,false]) ++ (rep [true,false,false,true,true,false] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (101+60*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n)) (phase9 n)) (phase10 n)) (phase11 n)) (phase12 n))
  rw [show 4+12*n+17+8*n+26+12*n+9+8*n+12+12*n+17+8*n+16=101+60*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 26 (fun n => 101+60*n) entry (by intro n; omega) growth m hm

#print axioms never

end M112

namespace M115

-- 1RB0RE_1RC1RB_0RD0LE_1LD0RA_1LC0LF_0LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,[],([true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩

theorem entry : run0 table 29 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨2,[],([true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨3,([true]) ++ (L),([false,false,false,true,false,false]) ++ ([false,true,false,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,false]) ++ (L),([false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,false,false,true,false,false] [false,true,false,false] [false,true,true,false] 4 local1 n (([false])) ([])

theorem phase2 (n : Nat) : run0 table 27 ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ = some ⟨4,([true,false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 4 ⟨4,([true,false,false,true,true,false,false,true,true,false]) ++ ([false,true,true,false]) ++ (L),(R)⟩ = some ⟨4,([true,false,false,true,true,false,false,true,true,false]) ++ (L),([false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (4*n) ⟨4,([true,false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ = some ⟨4,([true,false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,false,true,true,false,false,true,true,false] [] [false,true,true,false] [false,true,false,false] 4 local3 n (([false])) ([])

theorem phase4 (n : Nat) : run0 table 11 ⟨4,([true,false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ = some ⟨2,[],([true,false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) = ([true,false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (39+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 1+4*n+27+4*n+11=39+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 29 (fun n => 39+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M115

namespace M116

-- 1RB0RE_1RC1RE_0RD0LE_1LD0RA_1LC0LF_0LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,[],([true,false,false,false,true,false]) ++ (rep [false,false,true,false] (n))⟩

theorem entry : run0 table 21 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨2,[],([true,false,false,false,true,false]) ++ (rep [false,false,true,false] (n))⟩ = some ⟨3,([true,false]),([false,false,false,true,false]) ++ (rep [false,false,true,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨3,([true]) ++ (L),([false,false,false,true,false]) ++ ([false,false,true,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,false]) ++ (L),([false,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨3,([true,false]),([false,false,false,true,false]) ++ (rep [false,false,true,false] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,false,false,true,false] [false,false,true,false] [false,true,true,false] 4 local1 n (([false])) ([])

theorem phase2 (n : Nat) : run0 table 21 ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false])⟩ = some ⟨4,([false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 4 ⟨4,([false,true,true,false,false,true,true,false]) ++ ([false,true,true,false]) ++ (L),(R)⟩ = some ⟨4,([false,true,true,false,false,true,true,false]) ++ (L),([false,false,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (4*n) ⟨4,([false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false])⟩ = some ⟨4,([false,true,true,false,false,true,true,false,false]),(rep [false,false,false,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true,false,false,true,true,false] [] [false,true,true,false] [false,false,false,true] 4 local3 n (([false])) (([false]))

theorem phase4 (n : Nat) : run0 table 9 ⟨4,([false,true,true,false,false,true,true,false,false]),(rep [false,false,false,true] (n)) ++ ([false])⟩ = some ⟨2,[],([true,false,false,false,true,false,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,false,false,true,false,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([false]) = ([true,false,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false] (n)) := by
  calc
    _ = ([true,false,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,false,false,true,false,false,false,true])) ([]) [false,false,true] false n

theorem growth (n : Nat) : run0 table (31+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 1+4*n+21+4*n+9=31+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 21 (fun n => 31+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M116

namespace M127

-- 1RB0RE_1RC1RA_0RD---_1LD0RA_1RA0LF_0LF1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,([false,false,true,true,true]) ++ (rep [true,true] (n)) ++ ([false,true]),[]⟩

theorem entry : run0 table 17 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨3,([false,false,true,true,true]) ++ (rep [true,true] (n)) ++ ([false,true]),[]⟩ = some ⟨5,([true,true]) ++ (rep [true,true] (n)) ++ ([false,true]),([false,false,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨5,([true,true]) ++ ([true,true]) ++ (L),(R)⟩ = some ⟨5,([true,true]) ++ (L),([false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨5,([true,true]) ++ (rep [true,true] (n)) ++ ([false,true]),([false,false,false])⟩ = some ⟨5,([true,true,false,true]),(rep [false,true] (n)) ++ ([false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,true] [] [true,true] [false,true] 2 local1 n (([false,true])) (([false,false,false]))

theorem phase2 (n : Nat) : run0 table 7 ⟨5,([true,true,false,true]),(rep [false,true] (n)) ++ ([false,false,false])⟩ = some ⟨0,([false,true,false,true]),([true]) ++ (rep [false,true] (n)) ++ ([false,false,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 2 ⟨0,([false]) ++ (L),([true]) ++ ([false,true]) ++ (R)⟩ = some ⟨0,([false]) ++ ([true,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (2*n) ⟨0,([false,true,false,true]),([true]) ++ (rep [false,true] (n)) ++ ([false,false,false])⟩ = some ⟨0,([false]) ++ (rep [true,true] (n)) ++ ([true,false,true]),([true,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [false] [true] [false,true] [true,true] 2 local3 n (([true,false,true])) (([false,false,false]))

theorem phase4 (n : Nat) : run0 table 5 ⟨0,([false]) ++ (rep [true,true] (n)) ++ ([true,false,true]),([true,false,false,false])⟩ = some ⟨3,([false,false,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,false,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,false,true]) = ([false,false,true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false,true]) := by
  calc
    _ = ([false,false,true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,true,true,true])) (([false,true])) [true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (19+4*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 7+2*n+7+2*n+5=19+4*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 17 (fun n => 19+4*n) entry (by intro n; omega) growth m hm

#print axioms never

end M127

end BB6.Agent11Raw39B0REPumps
