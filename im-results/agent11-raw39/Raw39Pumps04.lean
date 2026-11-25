import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39Pumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M1769

-- 1RB1RB_1RC1LE_0RD1LC_1LD0RA_1LF1LF_0LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true,false]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true]),[]⟩

theorem entry : run0 table 38 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 11 ⟨1,([false,true,false]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true]),[]⟩ = some ⟨5,(rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true]),([true,true,false,true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨5,([false,true,true,false,true,true]) ++ (L),(R)⟩ = some ⟨5,(L),([true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨5,(rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true]),([true,true,false,true,true])⟩ = some ⟨5,([false,true,true,false,true]),(rep [true,true,false,true,true,false] (n)) ++ ([true,true,false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [] [] [false,true,true,false,true,true] [true,true,false,true,true,false] 6 local1 n (([false,true,true,false,true])) (([true,true,false,true,true]))

theorem phase2 (n : Nat) : run0 table 8 ⟨5,([false,true,true,false,true]),(rep [true,true,false,true,true,false] (n)) ++ ([true,true,false,true,true])⟩ = some ⟨2,([false,true]),([true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true,true,false,true,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 42 ⟨2,([false]) ++ (L),([true,true,false,true,true,false]) ++ ([true,true,false,true,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,true,true,false]) ++ (L),([true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (42*n) ⟨2,([false,true]),([true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true,true,false,true,true])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,true,false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true,true,false] [true,true,false,true,true,false] [true,true,false,true,true,false] 42 local3 n (([true])) (([true,true,false,true,true]))

theorem phase4 (n : Nat) : run0 table 66 ⟨2,([false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,true,false,true,true])⟩ = some ⟨1,([false,true,false,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]) = ([false,true,false,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true]) := by
  calc
    _ = ([false,true,false,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,true,true,false,true,true])) (([true])) [true,true,false,true,true] false n
    _ = ([false,true,false,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,true,true,false,true])) (([false,true])) [false,true,true,false,true] true n
    _ = ([false,true,false,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true,true,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,true,true,false])) (([true,false,true])) [true,false,true,true,false] true n
    _ = ([false,true,false,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,true,true])) (([true,true,false,true])) [true,true,false,true,true] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (85+48*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 11+6*n+8+42*n+66=85+48*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 38 (fun n => 85+48*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1769

namespace M1770

-- 1RB1RB_1RC1LE_0RD1LC_1LD0RA_1RB1LF_0LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true,false]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true]),[]⟩

theorem entry : run0 table 40 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 11 ⟨1,([false,true,false]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true]),[]⟩ = some ⟨1,([true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true]),([false,true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨1,([true,true]) ++ ([false,true,true,false,true,true]) ++ (L),(R)⟩ = some ⟨1,([true,true]) ++ (L),([false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨1,([true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true]),([false,true,true])⟩ = some ⟨1,([true,true,false,true,true,false,true]),(rep [false,true,true,false,true,true] (n)) ++ ([false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true] [] [false,true,true,false,true,true] [false,true,true,false,true,true] 6 local1 n (([false,true,true,false,true])) (([false,true,true]))

theorem phase2 (n : Nat) : run0 table 12 ⟨1,([true,true,false,true,true,false,true]),(rep [false,true,true,false,true,true] (n)) ++ ([false,true,true])⟩ = some ⟨2,([false,true]),([true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 42 ⟨2,([false]) ++ (L),([true,true,false,true,true,false,true,true]) ++ ([false,true,true,false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,true,true,false]) ++ (L),([true,true,false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (42*n) ⟨2,([false,true]),([true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,true,false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true,true,false,true,true] [false,true,true,false,true,true] [true,true,false,true,true,false] 42 local3 n (([true])) (([false,true,true]))

theorem phase4 (n : Nat) : run0 table 66 ⟨2,([false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,true,false,true,true])⟩ = some ⟨1,([false,true,false,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]) = ([false,true,false,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true]) := by
  calc
    _ = ([false,true,false,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,true,true,false,true,true])) (([true])) [true,true,false,true,true] false n
    _ = ([false,true,false,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,true,true,false,true])) (([false,true])) [false,true,true,false,true] true n
    _ = ([false,true,false,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true,true,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,true,true,false])) (([true,false,true])) [true,false,true,true,false] true n
    _ = ([false,true,false,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,true,true])) (([true,true,false,true])) [true,true,false,true,true] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (89+48*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 11+6*n+12+42*n+66=89+48*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 40 (fun n => 89+48*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1770

namespace M1788

-- 1RB1RB_1RC1LE_0RD0RC_1LD0RA_0LB1LF_1LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,(rep [false,false,false,false] (n)) ++ ([false,false,true,true]),[]⟩

theorem entry : run0 table 3 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 4 ⟨3,([false,false,false,false]) ++ (L),(R)⟩ = some ⟨3,(L),([true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (4*n) ⟨3,(rep [false,false,false,false] (n)) ++ ([false,false,true,true]),[]⟩ = some ⟨3,([false,false,true,true]),(rep [true,true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [] [] [false,false,false,false] [true,true,true,true] 4 local0 n (([false,false,true,true])) ([])

theorem phase1 (n : Nat) : run0 table 17 ⟨3,([false,false,true,true]),(rep [true,true,true,true] (n))⟩ = some ⟨2,([true,true,true]),([true,true,true]) ++ (rep [true,true,true,true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 4 ⟨2,([true]) ++ (L),([true,true,true]) ++ ([true,true,true,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([false,false,false,false]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (4*n) ⟨2,([true,true,true]),([true,true,true]) ++ (rep [true,true,true,true] (n))⟩ = some ⟨2,([true]) ++ (rep [false,false,false,false] (n)) ++ ([true,true]),([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true,true,true] [true,true,true,true] [false,false,false,false] 4 local2 n (([true,true])) ([])

theorem phase3 (n : Nat) : run0 table 5 ⟨2,([true]) ++ (rep [false,false,false,false] (n)) ++ ([true,true]),([true,true,true])⟩ = some ⟨3,([false,false,false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([true,true]) = ([false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([false,false,true,true]) := by
  calc
    _ = ([false,false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false])) (([true,true])) [false,false,false] false n
    _ = ([false,false,false,false]) ++ (rep [false,false,false,false] (n)) ++ ([false,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false])) (([false,true,true])) [false,false,false] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (22+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 4*n+17+4*n+5=22+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 3 (fun n => 22+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1788

namespace M1789

-- 1RB1RB_1RC1LE_0RD0RC_1LD0RA_0LF1LF_1LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,(rep [false,false,false,false,false,false,false] (n)) ++ ([false,false,true,true]),[]⟩

theorem entry : run0 table 3 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 7 ⟨3,([false,false,false,false,false,false,false]) ++ (L),(R)⟩ = some ⟨3,(L),([true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (7*n) ⟨3,(rep [false,false,false,false,false,false,false] (n)) ++ ([false,false,true,true]),[]⟩ = some ⟨3,([false,false,true,true]),(rep [true,true,true,true,true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [] [] [false,false,false,false,false,false,false] [true,true,true,true,true,true,true] 7 local0 n (([false,false,true,true])) ([])

theorem phase1 (n : Nat) : run0 table 19 ⟨3,([false,false,true,true]),(rep [true,true,true,true,true,true,true] (n))⟩ = some ⟨2,([true,true,false,true]),([true,true,true]) ++ (rep [true,true,true,true,true,true,true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 7 ⟨2,([true]) ++ (L),([true,true,true]) ++ ([true,true,true,true,true,true,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([false,false,false,false,false,false,false]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (7*n) ⟨2,([true,true,false,true]),([true,true,true]) ++ (rep [true,true,true,true,true,true,true] (n))⟩ = some ⟨2,([true]) ++ (rep [false,false,false,false,false,false,false] (n)) ++ ([true,false,true]),([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true,true,true] [true,true,true,true,true,true,true] [false,false,false,false,false,false,false] 7 local2 n (([true,false,true])) ([])

theorem phase3 (n : Nat) : run0 table 5 ⟨2,([true]) ++ (rep [false,false,false,false,false,false,false] (n)) ++ ([true,false,true]),([true,true,true])⟩ = some ⟨3,([false,false,false,false,false,false]) ++ (rep [false,false,false,false,false,false,false] (n)) ++ ([true,false,true]),[]⟩ := by rfl

theorem local4 (L R : List Bool) : run0 table 7 ⟨3,([false,false,false,false,false,false]) ++ ([false,false,false,false,false,false,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,false,false,false]) ++ (L),([true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase4 (n : Nat) : run0 table (7*n) ⟨3,([false,false,false,false,false,false]) ++ (rep [false,false,false,false,false,false,false] (n)) ++ ([true,false,true]),[]⟩ = some ⟨3,([false,false,false,false,false,false,true,false,true]),(rep [true,true,true,true,true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,false,false,false] [] [false,false,false,false,false,false,false] [true,true,true,true,true,true,true] 7 local4 n (([true,false,true])) ([])

theorem phase5 (n : Nat) : run0 table 12 ⟨3,([false,false,false,false,false,false,true,false,true]),(rep [true,true,true,true,true,true,true] (n))⟩ = some ⟨2,([true,true,true]),([true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true] (n))⟩ := by rfl

theorem local6 (L R : List Bool) : run0 table 7 ⟨2,([true]) ++ (L),([true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([false,false,false,false,false,false,false]) ++ (L),([true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase6 (n : Nat) : run0 table (7*n) ⟨2,([true,true,true]),([true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true] (n))⟩ = some ⟨2,([true]) ++ (rep [false,false,false,false,false,false,false] (n)) ++ ([true,true]),([true,true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true,true,true,true,true,true] [true,true,true,true,true,true,true] [false,false,false,false,false,false,false] 7 local6 n (([true,true])) ([])

theorem phase7 (n : Nat) : run0 table 8 ⟨2,([true]) ++ (rep [false,false,false,false,false,false,false] (n)) ++ ([true,true]),([true,true,true,true,true,true])⟩ = some ⟨3,([false,false,false,false,false,false,false,false,false]) ++ (rep [false,false,false,false,false,false,false] (n)) ++ ([true,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,false,false,false,false,false,false]) ++ (rep [false,false,false,false,false,false,false] (n)) ++ ([true,true]) = ([false,false,false,false,false,false,false]) ++ (rep [false,false,false,false,false,false,false] (n)) ++ ([false,false,true,true]) := by
  calc
    _ = ([false,false,false,false,false,false,false,false]) ++ (rep [false,false,false,false,false,false,false] (n)) ++ ([false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false,false,false,false])) (([true,true])) [false,false,false,false,false,false] false n
    _ = ([false,false,false,false,false,false,false]) ++ (rep [false,false,false,false,false,false,false] (n)) ++ ([false,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false,false,false])) (([false,true,true])) [false,false,false,false,false,false] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (44+28*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n))
  rw [finalL n] at H
  rw [show 7*n+19+7*n+5+7*n+12+7*n+8=44+28*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 3 (fun n => 44+28*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1789

namespace M1838

-- 1RB1RB_1RC1LE_0RD0RC_1LD0RA_1LF1RE_---0LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,(rep [false] (n)) ++ ([false,false,false,true,true,false]) ++ (rep [false,true] (n)) ++ ([false,true]),[]⟩

theorem entry : run0 table 22 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 1 ⟨3,([false]) ++ (L),(R)⟩ = some ⟨3,(L),([true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (1*n) ⟨3,(rep [false] (n)) ++ ([false,false,false,true,true,false]) ++ (rep [false,true] (n)) ++ ([false,true]),[]⟩ = some ⟨3,([false,false,false,true,true,false]) ++ (rep [false,true] (n)) ++ ([false,true]),(rep [true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [] [] [false] [true] 1 local0 n (([false,false,false,true,true,false]) ++ (rep [false,true] (n)) ++ ([false,true])) ([])

theorem phase1 (n : Nat) : run0 table 6 ⟨3,([false,false,false,true,true,false]) ++ (rep [false,true] (n)) ++ ([false,true]),(rep [true] (n))⟩ = some ⟨4,([true,false,true,false]) ++ (rep [false,true] (n)) ++ ([false,true]),([true,true]) ++ (rep [true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 1 ⟨4,([true]) ++ (L),([true,true]) ++ ([true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (1*n) ⟨4,([true,false,true,false]) ++ (rep [false,true] (n)) ++ ([false,true]),([true,true]) ++ (rep [true] (n))⟩ = some ⟨4,([true]) ++ (rep [true] (n)) ++ ([false,true,false]) ++ (rep [false,true] (n)) ++ ([false,true]),([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true,true] [true] [true] 1 local2 n (([false,true,false]) ++ (rep [false,true] (n)) ++ ([false,true])) ([])

theorem phase3 (n : Nat) : run0 table 3 ⟨4,([true]) ++ (rep [true] (n)) ++ ([false,true,false]) ++ (rep [false,true] (n)) ++ ([false,true]),([true,true])⟩ = some ⟨4,([false,true,true,true]) ++ (rep [true] (n)) ++ ([false,true,false]) ++ (rep [false,true] (n)) ++ ([false,true]),[]⟩ := by rfl

theorem local4 (L R : List Bool) : run0 table 5 ⟨4,([false,true,true,true]) ++ ([true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase4 (n : Nat) : run0 table (5*n) ⟨4,([false,true,true,true]) ++ (rep [true] (n)) ++ ([false,true,false]) ++ (rep [false,true] (n)) ++ ([false,true]),[]⟩ = some ⟨4,([false,true,true,true,false,true,false]) ++ (rep [false,true] (n)) ++ ([false,true]),(rep [true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true,true] [] [true] [true] 5 local4 n (([false,true,false]) ++ (rep [false,true] (n)) ++ ([false,true])) ([])

theorem phase5 (n : Nat) : run0 table 15 ⟨4,([false,true,true,true,false,true,false]) ++ (rep [false,true] (n)) ++ ([false,true]),(rep [true] (n))⟩ = some ⟨2,([true,true,true,false,false,true]) ++ (rep [false,true] (n)) ++ ([false,true]),([true]) ++ (rep [true] (n))⟩ := by rfl

theorem local6 (L R : List Bool) : run0 table 1 ⟨2,([true]) ++ (L),([true]) ++ ([true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase6 (n : Nat) : run0 table (1*n) ⟨2,([true,true,true,false,false,true]) ++ (rep [false,true] (n)) ++ ([false,true]),([true]) ++ (rep [true] (n))⟩ = some ⟨2,([true]) ++ (rep [false] (n)) ++ ([true,true,false,false,true]) ++ (rep [false,true] (n)) ++ ([false,true]),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true] [true] [false] 1 local6 n (([true,true,false,false,true]) ++ (rep [false,true] (n)) ++ ([false,true])) ([])

theorem phase7 (n : Nat) : run0 table 3 ⟨2,([true]) ++ (rep [false] (n)) ++ ([true,true,false,false,true]) ++ (rep [false,true] (n)) ++ ([false,true]),([true])⟩ = some ⟨3,([false,false,false,false]) ++ (rep [false] (n)) ++ ([true,true,false,false,true]) ++ (rep [false,true] (n)) ++ ([false,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,false]) ++ (rep [false] (n)) ++ ([true,true,false,false,true]) ++ (rep [false,true] (n)) ++ ([false,true]) = ([false]) ++ (rep [false] (n)) ++ ([false,false,false,true,true,false,false,true]) ++ (rep [false,true] (n)) ++ ([false,true]) := by
  calc
    _ = ([false,false,false]) ++ (rep [false] (n)) ++ ([false,true,true,false,false,true]) ++ (rep [false,true] (n)) ++ ([false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false])) (([true,true,false,false,true]) ++ (rep [false,true] (n)) ++ ([false,true])) [] false n
    _ = ([false,false]) ++ (rep [false] (n)) ++ ([false,false,true,true,false,false,true]) ++ (rep [false,true] (n)) ++ ([false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,true,true,false,false,true]) ++ (rep [false,true] (n)) ++ ([false,true])) [] false n
    _ = ([false]) ++ (rep [false] (n)) ++ ([false,false,false,true,true,false,false,true]) ++ (rep [false,true] (n)) ++ ([false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,true,true,false,false,true]) ++ (rep [false,true] (n)) ++ ([false,true])) [] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (27+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n))
  rw [finalL n] at H
  rw [show 1*n+6+1*n+3+5*n+15+1*n+3=27+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 22 (fun n => 27+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1838

namespace M1902

-- 1RB1RB_1RC1LF_0RD0RE_1LD0RA_0RB0RB_---0LD

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ = some ⟨3,([false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 7 ⟨3,([false,false,true]) ++ ([false,false,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true]) ++ (L),([true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (7*n) ⟨3,([false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ = some ⟨3,([false,false,true,true]) ++ (rep [false] (n)),(rep [true,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true] [] [false,false,true] [true,false,true] 7 local1 n (([true]) ++ (rep [false] (n))) ([])

theorem phase2 (n : Nat) : run0 table 9 ⟨3,([false,false,true,true]) ++ (rep [false] (n)),(rep [true,false,true] (n))⟩ = some ⟨1,([false,true,false]) ++ (rep [false] (n)),([true]) ++ (rep [true,false,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([false]) ++ (L),([true]) ++ ([true,false,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,false,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([false,true,false]) ++ (rep [false] (n)),([true]) ++ (rep [true,false,true] (n))⟩ = some ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true] [true,false,true] [false,false,true] 3 local3 n (([true,false]) ++ (rep [false] (n))) ([])

theorem phase4 (n : Nat) : run0 table 3 ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)),([true])⟩ = some ⟨1,([false,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)) = ([false,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (14+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 2+7*n+9+3*n+3=14+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 14+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1902

namespace M1908

-- 1RB1RB_1RC1LF_0RD0RE_1LD0RA_0RD0RB_---0LD

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,true,3⟩)
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ = some ⟨3,([false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 7 ⟨3,([false,false,true]) ++ ([false,false,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true]) ++ (L),([true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (7*n) ⟨3,([false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ = some ⟨3,([false,false,true,true]) ++ (rep [false,false] (n)),(rep [true,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true] [] [false,false,true] [true,false,true] 7 local1 n (([true]) ++ (rep [false,false] (n))) ([])

theorem phase2 (n : Nat) : run0 table 9 ⟨3,([false,false,true,true]) ++ (rep [false,false] (n)),(rep [true,false,true] (n))⟩ = some ⟨1,([false,true,false]) ++ (rep [false,false] (n)),([true]) ++ (rep [true,false,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([false]) ++ (L),([true]) ++ ([true,false,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,false,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([false,true,false]) ++ (rep [false,false] (n)),([true]) ++ (rep [true,false,true] (n))⟩ = some ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false,false] (n)),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true] [true,false,true] [false,false,true] 3 local3 n (([true,false]) ++ (rep [false,false] (n))) ([])

theorem phase4 (n : Nat) : run0 table 3 ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false,false] (n)),([true])⟩ = some ⟨3,([false,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false,false] (n)),[]⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 7 ⟨3,([false,false,false,true]) ++ ([false,false,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,true]) ++ (L),([false,true,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (7*n) ⟨3,([false,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false,false] (n)),[]⟩ = some ⟨3,([false,false,false,true,true,false]) ++ (rep [false,false] (n)),(rep [false,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,true] [] [false,false,true] [false,true,true] 7 local5 n (([true,false]) ++ (rep [false,false] (n))) ([])

theorem phase6 (n : Nat) : run0 table 10 ⟨3,([false,false,false,true,true,false]) ++ (rep [false,false] (n)),(rep [false,true,true] (n))⟩ = some ⟨1,([false,true,false,false]) ++ (rep [false,false] (n)),([true,true]) ++ (rep [false,true,true] (n))⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 3 ⟨1,([false]) ++ (L),([true,true]) ++ ([false,true,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,false,true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (3*n) ⟨1,([false,true,false,false]) ++ (rep [false,false] (n)),([true,true]) ++ (rep [false,true,true] (n))⟩ = some ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,true] [false,true,true] [false,false,true] 3 local7 n (([true,false,false]) ++ (rep [false,false] (n))) ([])

theorem phase8 (n : Nat) : run0 table 3 ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),([true,true])⟩ = some ⟨1,([false,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)) = ([false,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (27+20*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 2+7*n+9+3*n+3+7*n+10+3*n+3=27+20*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 27+20*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1908

namespace M1918

-- 1RB1RB_1RC1LF_0RD1RE_1LD0RA_0RC0RB_---0LD

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
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [true,false,true,false] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨1,([false]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [true,false,true,false] (n)),[]⟩ = some ⟨3,([false,false,true]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [true,false,true,false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨3,([false,false,true]) ++ ([false,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true]) ++ (L),([false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨3,([false,false,true]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [true,false,true,false] (n)),[]⟩ = some ⟨3,([false,false,true,true]) ++ (rep [true,false,true,false] (n)),(rep [false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true] [] [false,true] [false,true] 6 local1 n (([true]) ++ (rep [true,false,true,false] (n))) ([])

theorem phase2 (n : Nat) : run0 table 10 ⟨3,([false,false,true,true]) ++ (rep [true,false,true,false] (n)),(rep [false,true] (n))⟩ = some ⟨2,([true,true,true,false]) ++ (rep [true,false,true,false] (n)),(rep [false,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 2 ⟨2,([true]) ++ (L),([false,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([false,true]) ++ (L),(R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (2*n) ⟨2,([true,true,true,false]) ++ (rep [true,false,true,false] (n)),(rep [false,true] (n))⟩ = some ⟨2,([true]) ++ (rep [false,true] (n)) ++ ([true,true,false]) ++ (rep [true,false,true,false] (n)),[]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [] [false,true] [false,true] 2 local3 n (([true,true,false]) ++ (rep [true,false,true,false] (n))) ([])

theorem phase4 (n : Nat) : run0 table 4 ⟨2,([true]) ++ (rep [false,true] (n)) ++ ([true,true,false]) ++ (rep [true,false,true,false] (n)),[]⟩ = some ⟨3,([false,false,true]) ++ (rep [false,true] (n)) ++ ([true,true,false]) ++ (rep [true,false,true,false] (n)),([true])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 6 ⟨3,([false,false,true]) ++ ([false,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true]) ++ (L),([false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (6*n) ⟨3,([false,false,true]) ++ (rep [false,true] (n)) ++ ([true,true,false]) ++ (rep [true,false,true,false] (n)),([true])⟩ = some ⟨3,([false,false,true,true,true,false]) ++ (rep [true,false,true,false] (n)),(rep [false,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true] [] [false,true] [false,true] 6 local5 n (([true,true,false]) ++ (rep [true,false,true,false] (n))) (([true]))

theorem phase6 (n : Nat) : run0 table 10 ⟨3,([false,false,true,true,true,false]) ++ (rep [true,false,true,false] (n)),(rep [false,true] (n)) ++ ([true])⟩ = some ⟨2,([true,true,true,false,true,false]) ++ (rep [true,false,true,false] (n)),(rep [false,true] (n)) ++ ([true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 2 ⟨2,([true]) ++ (L),([false,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([false,true]) ++ (L),(R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (2*n) ⟨2,([true,true,true,false,true,false]) ++ (rep [true,false,true,false] (n)),(rep [false,true] (n)) ++ ([true])⟩ = some ⟨2,([true]) ++ (rep [false,true] (n)) ++ ([true,true,false,true,false]) ++ (rep [true,false,true,false] (n)),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [] [false,true] [false,true] 2 local7 n (([true,true,false,true,false]) ++ (rep [true,false,true,false] (n))) (([true]))

theorem phase8 (n : Nat) : run0 table 2 ⟨2,([true]) ++ (rep [false,true] (n)) ++ ([true,true,false,true,false]) ++ (rep [true,false,true,false] (n)),([true])⟩ = some ⟨1,([false,false,true]) ++ (rep [false,true] (n)) ++ ([true,true,false,true,false]) ++ (rep [true,false,true,false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true]) ++ (rep [false,true] (n)) ++ ([true,true,false,true,false]) ++ (rep [true,false,true,false] (n)) = ([false,false,true]) ++ (rep [false,true] (n)) ++ ([true,true,false,true,false]) ++ (rep [true,false,true,false] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (28+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 2+6*n+10+2*n+4+6*n+10+2*n+2=28+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 28+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1918

namespace M1921

-- 1RB1RB_1RC1LF_0RD0RA_1LD0RA_0LB---_0LB0LE

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
  | 4,false => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],(rep [true,false,false,true,true,false,false,true,false,false,true,true,false,false] (n)) ++ ([true,false,false,true])⟩

theorem entry : run0 table 11 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨5,[],(rep [true,false,false,true,true,false,false,true,false,false,true,true,false,false] (n)) ++ ([true,false,false,true])⟩ = some ⟨2,([false,true]),(rep [true,false,false,true,true,false,false,true,false,false,true,true,false,false] (n)) ++ ([true,false,false,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 14 ⟨2,([false]) ++ (L),([true,false,false,true,true,false,false,true,false,false,true,true,false,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,true,true,false,false,true,true,false,true,true,false,false]) ++ (L),(R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (14*n) ⟨2,([false,true]),(rep [true,false,false,true,true,false,false,true,false,false,true,true,false,false] (n)) ++ ([true,false,false,true])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,true,true,false,false,true,true,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [] [true,false,false,true,true,false,false,true,false,false,true,true,false,false] [true,true,false,true,true,false,false,true,true,false,true,true,false,false] 14 local1 n (([true])) (([true,false,false,true]))

theorem phase2 (n : Nat) : run0 table 17 ⟨2,([false]) ++ (rep [true,true,false,true,true,false,false,true,true,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true])⟩ = some ⟨1,([true,true,false,false]) ++ (rep [true,true,false,true,true,false,false,true,true,false,true,true,false,false] (n)) ++ ([true]),([false,true,false,false,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 30 ⟨1,([true,true,false,false]) ++ ([true,true,false,true,true,false,false,true,true,false,true,true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,false]) ++ (L),([false,false,true,false,false,true,true,false,false,true,false,false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (30*n) ⟨1,([true,true,false,false]) ++ (rep [true,true,false,true,true,false,false,true,true,false,true,true,false,false] (n)) ++ ([true]),([false,true,false,false,true])⟩ = some ⟨1,([true,true,false,false,true]),(rep [false,false,true,false,false,true,true,false,false,true,false,false,true,true] (n)) ++ ([false,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,false] [] [true,true,false,true,true,false,false,true,true,false,true,true,false,false] [false,false,true,false,false,true,true,false,false,true,false,false,true,true] 30 local3 n (([true])) (([false,true,false,false,true]))

theorem phase4 (n : Nat) : run0 table 15 ⟨1,([true,true,false,false,true]),(rep [false,false,true,false,false,true,true,false,false,true,false,false,true,true] (n)) ++ ([false,true,false,false,true])⟩ = some ⟨2,([false,true]),([true,false,false,true,true]) ++ (rep [false,false,true,false,false,true,true,false,false,true,false,false,true,true] (n)) ++ ([false,true,false,false,true])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 14 ⟨2,([false]) ++ (L),([true,false,false,true,true]) ++ ([false,false,true,false,false,true,true,false,false,true,false,false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,true,true,false,false,true,true,false,true,true,false,false]) ++ (L),([true,false,false,true,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (14*n) ⟨2,([false,true]),([true,false,false,true,true]) ++ (rep [false,false,true,false,false,true,true,false,false,true,false,false,true,true] (n)) ++ ([false,true,false,false,true])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,true,true,false,false,true,true,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,true,false,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true,true] [false,false,true,false,false,true,true,false,false,true,false,false,true,true] [true,true,false,true,true,false,false,true,true,false,true,true,false,false] 14 local5 n (([true])) (([false,true,false,false,true]))

theorem phase6 (n : Nat) : run0 table 23 ⟨2,([false]) ++ (rep [true,true,false,true,true,false,false,true,true,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,true,false,true,false,false,true])⟩ = some ⟨1,([true,true,false,true,true,false,true,true,false,false]) ++ (rep [true,true,false,true,true,false,false,true,true,false,true,true,false,false] (n)) ++ ([true]),([false,true,false,false,true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 30 ⟨1,([true,true,false,true,true,false,true,true,false,false]) ++ ([true,true,false,true,true,false,false,true,true,false,true,true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,true,true,false,true,true,false,false]) ++ (L),([true,false,false,true,false,false,true,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (30*n) ⟨1,([true,true,false,true,true,false,true,true,false,false]) ++ (rep [true,true,false,true,true,false,false,true,true,false,true,true,false,false] (n)) ++ ([true]),([false,true,false,false,true])⟩ = some ⟨1,([true,true,false,true,true,false,true,true,false,false,true]),(rep [true,false,false,true,false,false,true,true,false,false,true,false,false,true] (n)) ++ ([false,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,true,true,false,true,true,false,false] [] [true,true,false,true,true,false,false,true,true,false,true,true,false,false] [true,false,false,true,false,false,true,true,false,false,true,false,false,true] 30 local7 n (([true])) (([false,true,false,false,true]))

theorem phase8 (n : Nat) : run0 table 21 ⟨1,([true,true,false,true,true,false,true,true,false,false,true]),(rep [true,false,false,true,false,false,true,true,false,false,true,false,false,true] (n)) ++ ([false,true,false,false,true])⟩ = some ⟨2,([false,true]),([true,false,false,true,true,false,false,true,false,false,true]) ++ (rep [true,false,false,true,false,false,true,true,false,false,true,false,false,true] (n)) ++ ([false,true,false,false,true])⟩ := by rfl

theorem local9 (L R : List Bool) : run0 table 14 ⟨2,([false]) ++ (L),([true,false,false,true,true,false,false,true,false,false,true]) ++ ([true,false,false,true,false,false,true,true,false,false,true,false,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,true,true,false,false,true,true,false,true,true,false,false]) ++ (L),([true,false,false,true,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase9 (n : Nat) : run0 table (14*n) ⟨2,([false,true]),([true,false,false,true,true,false,false,true,false,false,true]) ++ (rep [true,false,false,true,false,false,true,true,false,false,true,false,false,true] (n)) ++ ([false,true,false,false,true])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,true,true,false,false,true,true,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,true,false,false,true,false,false,true,false,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true,true,false,false,true,false,false,true] [true,false,false,true,false,false,true,true,false,false,true,false,false,true] [true,true,false,true,true,false,false,true,true,false,true,true,false,false] 14 local9 n (([true])) (([false,true,false,false,true]))

theorem phase10 (n : Nat) : run0 table 13 ⟨2,([false]) ++ (rep [true,true,false,true,true,false,false,true,true,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,true,false,false,true,false,false,true,false,true,false,false,true])⟩ = some ⟨1,([true,true,false,true,true,false,false,true,true,false,true,true,false,false]) ++ (rep [true,true,false,true,true,false,false,true,true,false,true,true,false,false] (n)) ++ ([true]),([false,false,true])⟩ := by rfl

theorem local11 (L R : List Bool) : run0 table 30 ⟨1,([true,true,false,true,true,false,false,true,true,false,true,true,false,false]) ++ ([true,true,false,true,true,false,false,true,true,false,true,true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,true,true,false,false,true,true,false,true,true,false,false]) ++ (L),([false,false,true,true,false,false,true,false,false,true,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase11 (n : Nat) : run0 table (30*n) ⟨1,([true,true,false,true,true,false,false,true,true,false,true,true,false,false]) ++ (rep [true,true,false,true,true,false,false,true,true,false,true,true,false,false] (n)) ++ ([true]),([false,false,true])⟩ = some ⟨1,([true,true,false,true,true,false,false,true,true,false,true,true,false,false,true]),(rep [false,false,true,true,false,false,true,false,false,true,true,false,false,true] (n)) ++ ([false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,true,true,false,false,true,true,false,true,true,false,false] [] [true,true,false,true,true,false,false,true,true,false,true,true,false,false] [false,false,true,true,false,false,true,false,false,true,true,false,false,true] 30 local11 n (([true])) (([false,false,true]))

theorem phase12 (n : Nat) : run0 table 31 ⟨1,([true,true,false,true,true,false,false,true,true,false,true,true,false,false,true]),(rep [false,false,true,true,false,false,true,false,false,true,true,false,false,true] (n)) ++ ([false,false,true])⟩ = some ⟨5,[],([true,false,false,true,true,false,false,true,false,false,true,true,false,false,true]) ++ (rep [false,false,true,true,false,false,true,false,false,true,true,false,false,true] (n)) ++ ([false,false,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,false,true,true,false,false,true,false,false,true,true,false,false,true]) ++ (rep [false,false,true,true,false,false,true,false,false,true,true,false,false,true] (n)) ++ ([false,false,true]) = ([true,false,false,true,true,false,false,true,false,false,true,true,false,false]) ++ (rep [true,false,false,true,true,false,false,true,false,false,true,true,false,false] (n)) ++ ([true,false,false,true]) := by
  calc
    _ = ([true,false,false,true,true,false,false,true,false,false,true,true,false,false]) ++ (rep [true,false,false,true,true,false,false,true,false,false,true,true,false,false] (n)) ++ ([true,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,false,true,true,false,false,true,false,false,true,true,false,false])) (([false,false,true])) [false,false,true,true,false,false,true,false,false,true,true,false,false] true n

theorem growth (n : Nat) : run0 table (122+132*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n)) (phase9 n)) (phase10 n)) (phase11 n)) (phase12 n))
  rw [finalR n] at H
  rw [show 2+14*n+17+30*n+15+14*n+23+30*n+21+14*n+13+30*n+31=122+132*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 11 (fun n => 122+132*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1921

namespace M1922

-- 1RB1RB_1RC1LF_0RD0RC_1LD0RA_0LB---_0LB0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,(rep [false] (n)) ++ ([false,false,false,true,true,false,false]) ++ (rep [true] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 19 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 1 ⟨3,([false]) ++ (L),(R)⟩ = some ⟨3,(L),([true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (1*n) ⟨3,(rep [false] (n)) ++ ([false,false,false,true,true,false,false]) ++ (rep [true] (n)) ++ ([true]),[]⟩ = some ⟨3,([false,false,false,true,true,false,false]) ++ (rep [true] (n)) ++ ([true]),(rep [true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [] [] [false] [true] 1 local0 n (([false,false,false,true,true,false,false]) ++ (rep [true] (n)) ++ ([true])) ([])

theorem phase1 (n : Nat) : run0 table 15 ⟨3,([false,false,false,true,true,false,false]) ++ (rep [true] (n)) ++ ([true]),(rep [true] (n))⟩ = some ⟨2,([true,true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true]) ++ (rep [true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 1 ⟨2,([true]) ++ (L),([true]) ++ ([true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (1*n) ⟨2,([true,true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true]) ++ (rep [true] (n))⟩ = some ⟨2,([true]) ++ (rep [false] (n)) ++ ([true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true] [true] [false] 1 local2 n (([true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true])) ([])

theorem phase3 (n : Nat) : run0 table 3 ⟨2,([true]) ++ (rep [false] (n)) ++ ([true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true])⟩ = some ⟨3,([false,false,false,false]) ++ (rep [false] (n)) ++ ([true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,false]) ++ (rep [false] (n)) ++ ([true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true]) = ([false]) ++ (rep [false] (n)) ++ ([false,false,false,true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true]) := by
  calc
    _ = ([false,false,false]) ++ (rep [false] (n)) ++ ([false,true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false])) (([true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true])) [] false n
    _ = ([false,false]) ++ (rep [false] (n)) ++ ([false,false,true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true])) [] false n
    _ = ([false]) ++ (rep [false] (n)) ++ ([false,false,false,true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true])) [] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (18+2*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 1*n+15+1*n+3=18+2*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 19 (fun n => 18+2*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1922

end BB6.Agent11Raw39Pumps
