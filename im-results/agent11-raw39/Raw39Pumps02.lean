import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39Pumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M317

-- 1RB1RB_1RC0LF_0RD---_1LD0RA_1RF0LB_1LA1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [true,false,false,true] (n)) ++ ([true,false,false,true,true,false,false,true]),[]⟩

theorem entry : run0 table 28 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 9 ⟨1,([false]) ++ (rep [true,false,false,true] (n)) ++ ([true,false,false,true,true,false,false,true]),[]⟩ = some ⟨5,([true,true]) ++ (rep [true,false,false,true] (n)) ++ ([true,false,false,true,true,false,false,true]),([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨5,([true,true]) ++ ([true,false,false,true]) ++ (L),(R)⟩ = some ⟨5,([true,true]) ++ (L),([false,false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨5,([true,true]) ++ (rep [true,false,false,true] (n)) ++ ([true,false,false,true,true,false,false,true]),([false])⟩ = some ⟨5,([true,true,true,false,false,true,true,false,false,true]),(rep [false,false,false,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,true] [] [true,false,false,true] [false,false,false,true] 6 local1 n (([true,false,false,true,true,false,false,true])) (([false]))

theorem phase2 (n : Nat) : run0 table 15 ⟨5,([true,true,true,false,false,true,true,false,false,true]),(rep [false,false,false,true] (n)) ++ ([false])⟩ = some ⟨2,([false,true]),([true,false,false,false,true,false,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 4 ⟨2,([false]) ++ (L),([true,false,false,false,true,false,false,false,true]) ++ ([false,false,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false]) ++ (L),([true,false,false,false,true,false,false,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (4*n) ⟨2,([false,true]),([true,false,false,false,true,false,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([false])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false] (n)) ++ ([true]),([true,false,false,false,true,false,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,false,true,false,false,false,true] [false,false,false,true] [true,true,false,false] 4 local3 n (([true])) (([false]))

theorem phase4 (n : Nat) : run0 table 11 ⟨2,([false]) ++ (rep [true,true,false,false] (n)) ++ ([true]),([true,false,false,false,true,false,false,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true]) ++ (rep [true,false,false,true] (n)) ++ ([true,false,false,true,true,false,false,true]) := by
  calc
    _ = ([false,true,false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,false,true,true,false])) (([true])) [true,true,false] false n
    _ = ([false,true,false,false,true,true,false,false,true,true]) ++ (rep [false,false,true,true] (n)) ++ ([false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,false,true,true])) (([false,true])) [false,true,true] false n
    _ = ([false,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true] (n)) ++ ([true,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,false,true])) (([false,false,true])) [false,false,true] true n
    _ = ([false,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)) ++ ([true,true,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,false])) (([true,false,false,true])) [true,false,false] true n
    _ = ([false,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false,true,true,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false])) (([true,true,false,false,true])) [true,true,false] false n
    _ = ([false,true,false,false,true,true]) ++ (rep [false,false,true,true] (n)) ++ ([false,false,true,true,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true])) (([false,true,true,false,false,true])) [false,true,true] false n
    _ = ([false,true,false,false,true]) ++ (rep [true,false,false,true] (n)) ++ ([true,false,false,true,true,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true])) (([false,false,true,true,false,false,true])) [false,false,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (35+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 9+6*n+15+4*n+11=35+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 28 (fun n => 35+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M317

namespace M322

-- 1RB1RB_1RC0LF_0RD0RE_1LD0RA_0RC---_0LB1LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,true,true,false,false,true,true,false,false,true,true,true,false,false,true,true,false,false,true,true] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 84 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 391 ⟨1,([false,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,true,true,false,false,true,true,false,false,true,true,true,false,false,true,true,false,false,true,true] (n)) ++ ([true]),[]⟩ = some ⟨1,([false,true,false,false,true,true,false,false,true,true,false,false,true,true,true,true,false,false,true,true,false,false,true,true,true,false,false,true,true,false,false,true,true]) ++ (rep [true,true,true,true,false,false,true,true,false,false,true,true,true,false,false,true,true,false,false,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,true,false,false,true,true,false,false,true,true,true,true,false,false,true,true,false,false,true,true,true,false,false,true,true,false,false,true,true]) ++ (rep [true,true,true,true,false,false,true,true,false,false,true,true,true,false,false,true,true,false,false,true,true] (n)) ++ ([true]) = ([false,true,false,false,true,true,false,false,true,true,false,false,true,true,true,true,false,false,true,true,false,false,true,true,true,false,false,true,true,false,false,true,true]) ++ (rep [true,true,true,true,false,false,true,true,false,false,true,true,true,false,false,true,true,false,false,true,true] (n)) ++ ([true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (391+0*n) (family n) = some (family (n+1)) := by
  have H := (phase0 n)
  rw [show 391=391+0*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 84 (fun n => 391+0*n) entry (by intro n; omega) growth m hm

#print axioms never

end M322

namespace M481

-- 1RB1RB_1RC0RC_0RD1LE_1LD0RA_0LF---_1LC1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,([false]) ++ (rep [false,false,false,true,false,false,false,true] (n)) ++ ([false,false,false,true,false,false,false,true,false,false]),[]⟩

theorem entry : run0 table 42 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 14 ⟨0,([false]) ++ (rep [false,false,false,true,false,false,false,true] (n)) ++ ([false,false,false,true,false,false,false,true,false,false]),[]⟩ = some ⟨1,([true,true,false,false,true]) ++ (rep [false,false,false,true,false,false,false,true] (n)) ++ ([false,false,false,true,false,false,false,true,false,false]),([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 24 ⟨1,([true,true,false,false,true]) ++ ([false,false,false,true,false,false,false,true]) ++ (L),([true]) ++ (R)⟩ = some ⟨1,([true,true,false,false,true]) ++ (L),([true]) ++ ([false,true,false,true,false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (24*n) ⟨1,([true,true,false,false,true]) ++ (rep [false,false,false,true,false,false,false,true] (n)) ++ ([false,false,false,true,false,false,false,true,false,false]),([true])⟩ = some ⟨1,([true,true,false,false,true,false,false,false,true,false,false,false,true,false,false]),([true]) ++ (rep [false,true,false,true,false,true,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,false,true] [true] [false,false,false,true,false,false,false,true] [false,true,false,true,false,true,false,true] 24 local1 n (([false,false,false,true,false,false,false,true,false,false])) ([])

theorem phase2 (n : Nat) : run0 table 43 ⟨1,([true,true,false,false,true,false,false,false,true,false,false,false,true,false,false]),([true]) ++ (rep [false,true,false,true,false,true,false,true] (n))⟩ = some ⟨3,([true,false]),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 8 ⟨3,([true]) ++ (L),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]) ++ ([false,true,false,true,false,true,false,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,false,true,false,false,false,true,false]) ++ (L),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (8*n) ⟨3,([true,false]),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n))⟩ = some ⟨3,([true]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([false]),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true] [false,true,false,true,false,true,false,true] [false,false,true,false,false,false,true,false] 8 local3 n (([false])) ([])

theorem phase4 (n : Nat) : run0 table 17 ⟨3,([true]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([false]),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true])⟩ = some ⟨0,([false,false,false,false,true,false,false,false,true,false,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,false,true,false,false,false,true,false,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([false]) = ([false,false,false,false,true,false,false,false,true]) ++ (rep [false,false,false,true,false,false,false,true] (n)) ++ ([false,false,false,true,false,false,false,true,false,false]) := by
  calc
    _ = ([false,false,false,false,true,false,false,false,true,false,false,false,true,false,false,false,true]) ++ (rep [false,false,false,true,false,false,false,true] (n)) ++ ([false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,true,false,false,false,true,false,false,false,true,false,false,false,true])) (([false])) [false,false,true,false,false,false,true] false n
    _ = ([false,false,false,false,true,false,false,false,true,false,false,false,true,false,false,false]) ++ (rep [true,false,false,false,true,false,false,false] (n)) ++ ([true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,true,false,false,false,true,false,false,false,true,false,false,false])) (([false,false])) [false,false,false,true,false,false,false] true n
    _ = ([false,false,false,false,true,false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false,false,true,false,false] (n)) ++ ([false,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,true,false,false,false,true,false,false,false,true,false,false])) (([true,false,false])) [true,false,false,false,true,false,false] false n
    _ = ([false,false,false,false,true,false,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([false,false,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,true,false,false,false,true,false,false,false,true,false])) (([false,true,false,false])) [false,true,false,false,false,true,false] false n
    _ = ([false,false,false,false,true,false,false,false,true,false,false,false,true]) ++ (rep [false,false,false,true,false,false,false,true] (n)) ++ ([false,false,false,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,true,false,false,false,true,false,false,false,true])) (([false,false,true,false,false])) [false,false,true,false,false,false,true] false n
    _ = ([false,false,false,false,true,false,false,false,true,false,false,false]) ++ (rep [true,false,false,false,true,false,false,false] (n)) ++ ([true,false,false,false,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,true,false,false,false,true,false,false,false])) (([false,false,false,true,false,false])) [false,false,false,true,false,false,false] true n
    _ = ([false,false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false,false,true,false,false] (n)) ++ ([false,true,false,false,false,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,true,false,false,false,true,false,false])) (([true,false,false,false,true,false,false])) [true,false,false,false,true,false,false] false n
    _ = ([false,false,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([false,false,true,false,false,false,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,true,false,false,false,true,false])) (([false,true,false,false,false,true,false,false])) [false,true,false,false,false,true,false] false n
    _ = ([false,false,false,false,true,false,false,false,true]) ++ (rep [false,false,false,true,false,false,false,true] (n)) ++ ([false,false,false,true,false,false,false,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,true,false,false,false,true])) (([false,false,true,false,false,false,true,false,false])) [false,false,true,false,false,false,true] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (74+32*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 14+24*n+43+8*n+17=74+32*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 42 (fun n => 74+32*n) entry (by intro n; omega) growth m hm

#print axioms never

end M481

namespace M497

-- 1RB1RB_1RC0RC_0RD1LF_1LD0RA_1LC1LF_0LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,([false]) ++ (rep [false,false,false,true,false,false,false,true] (n)) ++ ([false,false,false,true,false,false,false,true,false,false]),[]⟩

theorem entry : run0 table 42 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 14 ⟨0,([false]) ++ (rep [false,false,false,true,false,false,false,true] (n)) ++ ([false,false,false,true,false,false,false,true,false,false]),[]⟩ = some ⟨1,([true,true,false,false,true]) ++ (rep [false,false,false,true,false,false,false,true] (n)) ++ ([false,false,false,true,false,false,false,true,false,false]),([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 24 ⟨1,([true,true,false,false,true]) ++ ([false,false,false,true,false,false,false,true]) ++ (L),([true]) ++ (R)⟩ = some ⟨1,([true,true,false,false,true]) ++ (L),([true]) ++ ([false,true,false,true,false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (24*n) ⟨1,([true,true,false,false,true]) ++ (rep [false,false,false,true,false,false,false,true] (n)) ++ ([false,false,false,true,false,false,false,true,false,false]),([true])⟩ = some ⟨1,([true,true,false,false,true,false,false,false,true,false,false,false,true,false,false]),([true]) ++ (rep [false,true,false,true,false,true,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,false,true] [true] [false,false,false,true,false,false,false,true] [false,true,false,true,false,true,false,true] 24 local1 n (([false,false,false,true,false,false,false,true,false,false])) ([])

theorem phase2 (n : Nat) : run0 table 43 ⟨1,([true,true,false,false,true,false,false,false,true,false,false,false,true,false,false]),([true]) ++ (rep [false,true,false,true,false,true,false,true] (n))⟩ = some ⟨3,([true,false]),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 8 ⟨3,([true]) ++ (L),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]) ++ ([false,true,false,true,false,true,false,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,false,true,false,false,false,true,false]) ++ (L),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (8*n) ⟨3,([true,false]),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n))⟩ = some ⟨3,([true]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([false]),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true] [false,true,false,true,false,true,false,true] [false,false,true,false,false,false,true,false] 8 local3 n (([false])) ([])

theorem phase4 (n : Nat) : run0 table 17 ⟨3,([true]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([false]),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true])⟩ = some ⟨0,([false,false,false,false,true,false,false,false,true,false,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,false,true,false,false,false,true,false,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([false]) = ([false,false,false,false,true,false,false,false,true]) ++ (rep [false,false,false,true,false,false,false,true] (n)) ++ ([false,false,false,true,false,false,false,true,false,false]) := by
  calc
    _ = ([false,false,false,false,true,false,false,false,true,false,false,false,true,false,false,false,true]) ++ (rep [false,false,false,true,false,false,false,true] (n)) ++ ([false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,true,false,false,false,true,false,false,false,true,false,false,false,true])) (([false])) [false,false,true,false,false,false,true] false n
    _ = ([false,false,false,false,true,false,false,false,true,false,false,false,true,false,false,false]) ++ (rep [true,false,false,false,true,false,false,false] (n)) ++ ([true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,true,false,false,false,true,false,false,false,true,false,false,false])) (([false,false])) [false,false,false,true,false,false,false] true n
    _ = ([false,false,false,false,true,false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false,false,true,false,false] (n)) ++ ([false,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,true,false,false,false,true,false,false,false,true,false,false])) (([true,false,false])) [true,false,false,false,true,false,false] false n
    _ = ([false,false,false,false,true,false,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([false,false,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,true,false,false,false,true,false,false,false,true,false])) (([false,true,false,false])) [false,true,false,false,false,true,false] false n
    _ = ([false,false,false,false,true,false,false,false,true,false,false,false,true]) ++ (rep [false,false,false,true,false,false,false,true] (n)) ++ ([false,false,false,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,true,false,false,false,true,false,false,false,true])) (([false,false,true,false,false])) [false,false,true,false,false,false,true] false n
    _ = ([false,false,false,false,true,false,false,false,true,false,false,false]) ++ (rep [true,false,false,false,true,false,false,false] (n)) ++ ([true,false,false,false,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,true,false,false,false,true,false,false,false])) (([false,false,false,true,false,false])) [false,false,false,true,false,false,false] true n
    _ = ([false,false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false,false,true,false,false] (n)) ++ ([false,true,false,false,false,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,true,false,false,false,true,false,false])) (([true,false,false,false,true,false,false])) [true,false,false,false,true,false,false] false n
    _ = ([false,false,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([false,false,true,false,false,false,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,true,false,false,false,true,false])) (([false,true,false,false,false,true,false,false])) [false,true,false,false,false,true,false] false n
    _ = ([false,false,false,false,true,false,false,false,true]) ++ (rep [false,false,false,true,false,false,false,true] (n)) ++ ([false,false,false,true,false,false,false,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,true,false,false,false,true])) (([false,false,true,false,false,false,true,false,false])) [false,false,true,false,false,false,true] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (74+32*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 14+24*n+43+8*n+17=74+32*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 42 (fun n => 74+32*n) entry (by intro n; omega) growth m hm

#print axioms never

end M497

namespace M551

-- 1RB1RB_1RC0RE_0RD0RB_1LD0RA_0LF0RC_0LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true]) ++ (rep [false,false,false] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩

theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 10 ⟨2,([false,true]) ++ (rep [false,false,false] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ = some ⟨3,([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨3,([false,false,false,false]) ++ ([false,false,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,false]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨3,([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ = some ⟨3,([false,false,false,false,true]) ++ (rep [false] (n)),(rep [true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,false] [] [false,false,false] [true,true,true] 3 local1 n (([true]) ++ (rep [false] (n))) ([])

theorem phase2 (n : Nat) : run0 table 6 ⟨3,([false,false,false,false,true]) ++ (rep [false] (n)),(rep [true,true,true] (n))⟩ = some ⟨1,([true,true,false]) ++ (rep [false] (n)),([true,true]) ++ (rep [true,true,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([true]) ++ (L),([true,true]) ++ ([true,true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([false,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([true,true,false]) ++ (rep [false] (n)),([true,true]) ++ (rep [true,true,true] (n))⟩ = some ⟨1,([true]) ++ (rep [false,false,false] (n)) ++ ([true,false]) ++ (rep [false] (n)),([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,true] [true,true,true] [false,false,false] 3 local3 n (([true,false]) ++ (rep [false] (n))) ([])

theorem phase4 (n : Nat) : run0 table 4 ⟨1,([true]) ++ (rep [false,false,false] (n)) ++ ([true,false]) ++ (rep [false] (n)),([true,true])⟩ = some ⟨2,([false,true,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,false]) ++ (rep [false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,false]) ++ (rep [false] (n)) = ([false,true,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,false]) ++ (rep [false] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (20+6*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 10+3*n+6+3*n+4=20+6*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 20+6*n) entry (by intro n; omega) growth m hm

#print axioms never

end M551

namespace M728

-- 1RB1RB_1RC0RE_0RD0RF_1LD0RA_1LE0LD_---1RC

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,4⟩)
  | 4,true => some (some ⟨false,false,3⟩)
  | 5,true => some (some ⟨true,true,2⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false,false,true,false]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 8 ⟨4,([false,false,true,false]) ++ ([false,true]) ++ (L),(R)⟩ = some ⟨4,([false,false,true,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (8*n) ⟨4,([false,false,true,false]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ = some ⟨4,([false,false,true,false,true]) ++ (rep [false] (n)),(rep [true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,false,true,false] [] [false,true] [true,true] 8 local0 n (([true]) ++ (rep [false] (n))) ([])

theorem phase1 (n : Nat) : run0 table 7 ⟨4,([false,false,true,false,true]) ++ (rep [false] (n)),(rep [true,true] (n))⟩ = some ⟨2,([true,true,true,false]) ++ (rep [false] (n)),([true]) ++ (rep [true,true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 2 ⟨2,([true]) ++ (L),([true]) ++ ([true,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (2*n) ⟨2,([true,true,true,false]) ++ (rep [false] (n)),([true]) ++ (rep [true,true] (n))⟩ = some ⟨2,([true]) ++ (rep [true,false] (n)) ++ ([true,true,false]) ++ (rep [false] (n)),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true] [true,true] [true,false] 2 local2 n (([true,true,false]) ++ (rep [false] (n))) ([])

theorem phase3 (n : Nat) : run0 table 8 ⟨2,([true]) ++ (rep [true,false] (n)) ++ ([true,true,false]) ++ (rep [false] (n)),([true])⟩ = some ⟨4,([false,false,true,false,false]) ++ (rep [true,false] (n)) ++ ([true,true,false]) ++ (rep [false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true,false,false]) ++ (rep [true,false] (n)) ++ ([true,true,false]) ++ (rep [false] (n)) = ([false,false,true,false,false,true]) ++ (rep [false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)) := by
  calc
    _ = ([false,false,true,false,false,true]) ++ (rep [false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,false,false])) (([true,false]) ++ (rep [false] (n))) [false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (15+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 8*n+7+2*n+8=15+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (fun n => 15+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M728

namespace M852

-- 1RB1RB_1RC0RF_0RD0RB_1LD0RA_0LF---_0LE0RC

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true]) ++ (rep [false,false,false] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩

theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 10 ⟨2,([false,true]) ++ (rep [false,false,false] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ = some ⟨3,([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨3,([false,false,false,false]) ++ ([false,false,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,false]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨3,([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ = some ⟨3,([false,false,false,false,true]) ++ (rep [false] (n)),(rep [true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,false] [] [false,false,false] [true,true,true] 3 local1 n (([true]) ++ (rep [false] (n))) ([])

theorem phase2 (n : Nat) : run0 table 6 ⟨3,([false,false,false,false,true]) ++ (rep [false] (n)),(rep [true,true,true] (n))⟩ = some ⟨1,([true,true,false]) ++ (rep [false] (n)),([true,true]) ++ (rep [true,true,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([true]) ++ (L),([true,true]) ++ ([true,true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([false,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([true,true,false]) ++ (rep [false] (n)),([true,true]) ++ (rep [true,true,true] (n))⟩ = some ⟨1,([true]) ++ (rep [false,false,false] (n)) ++ ([true,false]) ++ (rep [false] (n)),([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,true] [true,true,true] [false,false,false] 3 local3 n (([true,false]) ++ (rep [false] (n))) ([])

theorem phase4 (n : Nat) : run0 table 4 ⟨1,([true]) ++ (rep [false,false,false] (n)) ++ ([true,false]) ++ (rep [false] (n)),([true,true])⟩ = some ⟨2,([false,true,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,false]) ++ (rep [false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,false]) ++ (rep [false] (n)) = ([false,true,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,false]) ++ (rep [false] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (20+6*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 10+3*n+6+3*n+4=20+6*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 20+6*n) entry (by intro n; omega) growth m hm

#print axioms never

end M852

namespace M1093

-- 1RB1RB_1RC0RF_0RD0RE_1LD0RA_---1RC_1LF0LD

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨true,true,2⟩)
  | 5,false => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,([false,false,true,false]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 8 ⟨5,([false,false,true,false]) ++ ([false,true]) ++ (L),(R)⟩ = some ⟨5,([false,false,true,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (8*n) ⟨5,([false,false,true,false]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ = some ⟨5,([false,false,true,false,true]) ++ (rep [false] (n)),(rep [true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,true,false] [] [false,true] [true,true] 8 local0 n (([true]) ++ (rep [false] (n))) ([])

theorem phase1 (n : Nat) : run0 table 7 ⟨5,([false,false,true,false,true]) ++ (rep [false] (n)),(rep [true,true] (n))⟩ = some ⟨2,([true,true,true,false]) ++ (rep [false] (n)),([true]) ++ (rep [true,true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 2 ⟨2,([true]) ++ (L),([true]) ++ ([true,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (2*n) ⟨2,([true,true,true,false]) ++ (rep [false] (n)),([true]) ++ (rep [true,true] (n))⟩ = some ⟨2,([true]) ++ (rep [true,false] (n)) ++ ([true,true,false]) ++ (rep [false] (n)),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true] [true,true] [true,false] 2 local2 n (([true,true,false]) ++ (rep [false] (n))) ([])

theorem phase3 (n : Nat) : run0 table 8 ⟨2,([true]) ++ (rep [true,false] (n)) ++ ([true,true,false]) ++ (rep [false] (n)),([true])⟩ = some ⟨5,([false,false,true,false,false]) ++ (rep [true,false] (n)) ++ ([true,true,false]) ++ (rep [false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true,false,false]) ++ (rep [true,false] (n)) ++ ([true,true,false]) ++ (rep [false] (n)) = ([false,false,true,false,false,true]) ++ (rep [false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)) := by
  calc
    _ = ([false,false,true,false,false,true]) ++ (rep [false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,false,false])) (([true,false]) ++ (rep [false] (n))) [false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (15+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 8*n+7+2*n+8=15+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (fun n => 15+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1093

namespace M1357

-- 1RB1RB_1RC1LB_0RD1RE_1LD0RA_0RF1LF_---0LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true,false,false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true]),[]⟩

theorem entry : run0 table 67 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 35 ⟨1,([false,true,false,false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true]),[]⟩ = some ⟨1,([true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true]),([false,true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨1,([true,true,true]) ++ ([true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨1,([true,true,true]) ++ (L),([true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨1,([true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true]),([false,true,true])⟩ = some ⟨1,([true,true,true,true,true,true,true,true,true]),(rep [true,true,true,true,true,true] (n)) ++ ([false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,true] [] [true,true,true,true,true,true] [true,true,true,true,true,true] 6 local1 n (([true,true,true,true,true,true])) (([false,true,true]))

theorem phase2 (n : Nat) : run0 table 15 ⟨1,([true,true,true,true,true,true,true,true,true]),(rep [true,true,true,true,true,true] (n)) ++ ([false,true,true])⟩ = some ⟨2,([true,true]),([false,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false,true,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 30 ⟨2,([true]) ++ (L),([false,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true,true,true,true,true]) ++ (L),([false,true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (30*n) ⟨2,([true,true]),([false,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false,true,true])⟩ = some ⟨2,([true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),([false,true,true,true,true,true,true,true,true,false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,true,true,true,true,true,true,true,true] [true,true,true,true,true,true] [true,true,true,true,true,true] 30 local3 n (([true])) (([false,true,true]))

theorem phase4 (n : Nat) : run0 table 52 ⟨2,([true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),([false,true,true,true,true,true,true,true,true,false,true,true])⟩ = some ⟨1,([false,true,false,false,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]) = ([false,true,false,false,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true]) := by
  calc
    _ = ([false,true,false,false,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,true,true,true,true,true,true,true,true])) (([true])) [true,true,true,true,true] true n
    _ = ([false,true,false,false,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,true,true,true,true,true,true,true])) (([true,true])) [true,true,true,true,true] true n
    _ = ([false,true,false,false,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,true,true,true,true,true,true])) (([true,true,true])) [true,true,true,true,true] true n
    _ = ([false,true,false,false,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,true,true,true,true,true])) (([true,true,true,true])) [true,true,true,true,true] true n
    _ = ([false,true,false,false,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,true,true,true,true])) (([true,true,true,true,true])) [true,true,true,true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (102+36*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 35+6*n+15+30*n+52=102+36*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 67 (fun n => 102+36*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1357

namespace M1419

-- 1RB1RB_1RC1LB_0RD1RF_1LD0RA_---0LB_0RE1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨false,true,4⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true,false,false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true]),[]⟩

theorem entry : run0 table 67 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 35 ⟨1,([false,true,false,false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true]),[]⟩ = some ⟨1,([true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true]),([false,true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨1,([true,true,true]) ++ ([true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨1,([true,true,true]) ++ (L),([true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨1,([true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true]),([false,true,true])⟩ = some ⟨1,([true,true,true,true,true,true,true,true,true]),(rep [true,true,true,true,true,true] (n)) ++ ([false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,true] [] [true,true,true,true,true,true] [true,true,true,true,true,true] 6 local1 n (([true,true,true,true,true,true])) (([false,true,true]))

theorem phase2 (n : Nat) : run0 table 15 ⟨1,([true,true,true,true,true,true,true,true,true]),(rep [true,true,true,true,true,true] (n)) ++ ([false,true,true])⟩ = some ⟨2,([true,true]),([false,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false,true,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 30 ⟨2,([true]) ++ (L),([false,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true,true,true,true,true]) ++ (L),([false,true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (30*n) ⟨2,([true,true]),([false,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false,true,true])⟩ = some ⟨2,([true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),([false,true,true,true,true,true,true,true,true,false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,true,true,true,true,true,true,true,true] [true,true,true,true,true,true] [true,true,true,true,true,true] 30 local3 n (([true])) (([false,true,true]))

theorem phase4 (n : Nat) : run0 table 52 ⟨2,([true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),([false,true,true,true,true,true,true,true,true,false,true,true])⟩ = some ⟨1,([false,true,false,false,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]) = ([false,true,false,false,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true]) := by
  calc
    _ = ([false,true,false,false,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,true,true,true,true,true,true,true,true])) (([true])) [true,true,true,true,true] true n
    _ = ([false,true,false,false,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,true,true,true,true,true,true,true])) (([true,true])) [true,true,true,true,true] true n
    _ = ([false,true,false,false,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,true,true,true,true,true,true])) (([true,true,true])) [true,true,true,true,true] true n
    _ = ([false,true,false,false,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,true,true,true,true,true])) (([true,true,true,true])) [true,true,true,true,true] true n
    _ = ([false,true,false,false,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,true,true,true,true])) (([true,true,true,true,true])) [true,true,true,true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (102+36*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 35+6*n+15+30*n+52=102+36*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 67 (fun n => 102+36*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1419

end BB6.Agent11Raw39Pumps
