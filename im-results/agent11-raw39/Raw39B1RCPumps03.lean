import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B1RCPumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M133

-- 1RB1RC_1RC1RC_0RD0LE_1LD0RA_0LA1LF_0LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,([false,false,true,true]) ++ (rep [false,false,true,true] (n)),[]⟩

theorem entry : run0 table 3 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 12 ⟨3,([false,false,true,true]) ++ ([false,false,true,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true]) ++ (L),([true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (12*n) ⟨3,([false,false,true,true]) ++ (rep [false,false,true,true] (n)),[]⟩ = some ⟨3,([false,false,true,true]),(rep [true,false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true] [] [false,false,true,true] [true,false,true,false] 12 local0 n ([]) ([])

theorem phase1 (n : Nat) : run0 table 12 ⟨3,([false,false,true,true]),(rep [true,false,true,false] (n))⟩ = some ⟨2,([false,true,true]),([true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 4 ⟨2,([false]) ++ (L),([true,false,true,false]) ++ ([true,false,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false]) ++ (L),([true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (4*n) ⟨2,([false,true,true]),([true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false] (n)) ++ ([true,true]),([true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,true,false] [true,false,true,false] [true,true,false,false] 4 local2 n (([true,true])) ([])

theorem phase3 (n : Nat) : run0 table 5 ⟨2,([false]) ++ (rep [true,true,false,false] (n)) ++ ([true,true]),([true,false,true,false])⟩ = some ⟨3,([false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)) ++ ([true,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)) ++ ([true,true]) = ([false,false,true,true,false,false,true,true]) ++ (rep [false,false,true,true] (n)) := by
  calc
    _ = ([false,false,true,true,false,false,true]) ++ (rep [true,false,false,true] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,true,false,false])) (([true])) [true,false,false] true n
    _ = ([false,false,true,true,false,false,true,true]) ++ (rep [false,false,true,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,true,false,false,true])) ([]) [false,false,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (17+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 12*n+12+4*n+5=17+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 3 (fun n => 17+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M133

namespace M134

-- 1RB1RC_1RC1RE_0RD0LE_1LD0RA_0LA1LF_0LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,([false,false,true,true]) ++ (rep [false,false,true,true] (n)),[]⟩

theorem entry : run0 table 3 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 12 ⟨3,([false,false,true,true]) ++ ([false,false,true,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true]) ++ (L),([true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (12*n) ⟨3,([false,false,true,true]) ++ (rep [false,false,true,true] (n)),[]⟩ = some ⟨3,([false,false,true,true]),(rep [true,false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true] [] [false,false,true,true] [true,false,true,false] 12 local0 n ([]) ([])

theorem phase1 (n : Nat) : run0 table 12 ⟨3,([false,false,true,true]),(rep [true,false,true,false] (n))⟩ = some ⟨2,([false,true,true]),([true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 6 ⟨2,([false]) ++ (L),([true,false,true,false]) ++ ([true,false,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false]) ++ (L),([true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (6*n) ⟨2,([false,true,true]),([true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false] (n)) ++ ([true,true]),([true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,true,false] [true,false,true,false] [true,true,false,false] 6 local2 n (([true,true])) ([])

theorem phase3 (n : Nat) : run0 table 7 ⟨2,([false]) ++ (rep [true,true,false,false] (n)) ++ ([true,true]),([true,false,true,false])⟩ = some ⟨3,([false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)) ++ ([true,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)) ++ ([true,true]) = ([false,false,true,true,false,false,true,true]) ++ (rep [false,false,true,true] (n)) := by
  calc
    _ = ([false,false,true,true,false,false,true]) ++ (rep [true,false,false,true] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,true,false,false])) (([true])) [true,false,false] true n
    _ = ([false,false,true,true,false,false,true,true]) ++ (rep [false,false,true,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,true,false,false,true])) ([]) [false,false,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (19+18*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 12*n+12+6*n+7=19+18*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 3 (fun n => 19+18*n) entry (by intro n; omega) growth m hm

#print axioms never

end M134

namespace M139

-- 1RB1RC_1RC0LC_0RD0LE_1LD0RA_1LC1LF_0LE---

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
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,[],([true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨2,[],([true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩ = some ⟨3,([true,false]),([false,true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 10 ⟨3,([true,false]) ++ (L),([false,true,false,true,false]) ++ ([true,false,true,false]) ++ (R)⟩ = some ⟨3,([true,false]) ++ ([true,true,false,false]) ++ (L),([false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (10*n) ⟨3,([true,false]),([false,true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩ = some ⟨3,([true,false]) ++ (rep [true,true,false,false] (n)),([false,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true,false] [false,true,false,true,false] [true,false,true,false] [true,true,false,false] 10 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 21 ⟨3,([true,false]) ++ (rep [true,true,false,false] (n)),([false,true,false,true,false])⟩ = some ⟨4,([true,false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)),([false,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 4 ⟨4,([true,false,false,true,true,false,false]) ++ ([true,true,false,false]) ++ (L),(R)⟩ = some ⟨4,([true,false,false,true,true,false,false]) ++ (L),([false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (4*n) ⟨4,([true,false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)),([false,true,false])⟩ = some ⟨4,([true,false,false,true,true,false,false]),(rep [false,true,false,true] (n)) ++ ([false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,false,true,true,false,false] [] [true,true,false,false] [false,true,false,true] 4 local3 n ([]) (([false,true,false]))

theorem phase4 (n : Nat) : run0 table 7 ⟨4,([true,false,false,true,true,false,false]),(rep [false,true,false,true] (n)) ++ ([false,true,false])⟩ = some ⟨2,[],([true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([false,true,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([false,true,false]) = ([true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) := by
  calc
    _ = ([true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,false,true,false,true])) (([true,false])) [true,false,true] false n
    _ = ([true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,false,true,false,true,false])) (([false])) [false,true,false] true n
    _ = ([true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,false,true,false,true,false,true])) ([]) [true,false,true] false n

theorem growth (n : Nat) : run0 table (29+14*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 1+10*n+21+4*n+7=29+14*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 29+14*n) entry (by intro n; omega) growth m hm

#print axioms never

end M139

namespace M148

-- 1RB1RC_1RC1LC_0RD0LE_1LD0RA_1RC1LF_1LA---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,true,2⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 10 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨2,([true,true]) ++ (rep [false,false,true,false,false,true] (n)),([true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 10 ⟨2,([true,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨2,([true,true]) ++ (L),([true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (10*n) ⟨2,([true,true]) ++ (rep [false,false,true,false,false,true] (n)),([true,false])⟩ = some ⟨2,([true,true]),(rep [true,true,false,true,true,false] (n)) ++ ([true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 2 [true,true] [] [false,false,true,false,false,true] [true,true,false,true,true,false] 10 local1 n ([]) (([true,false]))

theorem phase2 (n : Nat) : run0 table 7 ⟨2,([true,true]),(rep [true,true,false,true,true,false] (n)) ++ ([true,false])⟩ = some ⟨2,([false,true]),([true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨2,([false]) ++ (L),([true,true,false]) ++ ([true,true,false,true,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨2,([false,true]),([true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true,false])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false] [true,true,false,true,true,false] [true,false,false,true,false,false] 6 local3 n (([true])) (([true,false]))

theorem phase4 (n : Nat) : run0 table 6 ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false])) ([]) [false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (23+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 10+10*n+7+6*n+6=23+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 23+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M148

namespace M155

-- 1RB1RC_1RC---_0RD0LE_1LD0RA_1RB1LF_1LC1LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false]),[]⟩

theorem entry : run0 table 40 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 8 ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false]),[]⟩ = some ⟨5,([false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false]),([true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 7 ⟨5,([false,true,false,false,true,false,false]) ++ ([true,false,false]) ++ (L),(R)⟩ = some ⟨5,([false,true,false,false,true,false,false]) ++ (L),([true,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (7*n) ⟨5,([false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false]),([true,false])⟩ = some ⟨5,([false,true,false,false,true,false,false,false]),(rep [true,true,false] (n)) ++ ([true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true,false,false,true,false,false] [] [true,false,false] [true,true,false] 7 local1 n (([false])) (([true,false]))

theorem phase2 (n : Nat) : run0 table 32 ⟨5,([false,true,false,false,true,false,false,false]),(rep [true,true,false] (n)) ++ ([true,false])⟩ = some ⟨2,([false,false]),([true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨2,([false]) ++ (L),([true,true,false,true,true,false]) ++ ([true,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false]) ++ (L),([true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨2,([false,false]),([true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true,false])⟩ = some ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([false]),([true,true,false,true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true,true,false] [true,true,false] [true,false,false] 3 local3 n (([false])) (([true,false]))

theorem phase4 (n : Nat) : run0 table 9 ⟨2,([false]) ++ (rep [true,false,false] (n)) ++ ([false]),([true,true,false,true,true,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false]) = ([false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (49+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 8+7*n+32+3*n+9=49+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 40 (fun n => 49+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M155

namespace M156

-- 1RB1RC_1RC0LB_0RD0LE_1LD0RA_0LB1LF_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 42 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 9 ⟨1,([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),[]⟩ = some ⟨4,([true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),([true,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 33 ⟨4,([true,false,false,true,false,false,true,false,false,true]) ++ ([false,false,true,false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨4,([true,false,false,true,false,false,true,false,false,true]) ++ (L),([false,true,true,false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (33*n) ⟨4,([true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),([true,true,false])⟩ = some ⟨4,([true,false,false,true,false,false,true,false,false,true]),(rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,false,true,false,false,true,false,false,true] [] [false,false,true,false,false,true,false,false,true] [false,true,true,false,true,true,false,true,true] 33 local1 n ([]) (([true,true,false]))

theorem phase2 (n : Nat) : run0 table 37 ⟨4,([true,false,false,true,false,false,true,false,false,true]),(rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ = some ⟨2,([false,true]),([true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 9 ⟨2,([false]) ++ (L),([true,true,false,true,true,false,true,true,false,true,true]) ++ ([false,true,true,false,true,true,false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false,true,false,false]) ++ (L),([true,true,false,true,true,false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (9*n) ⟨2,([false,true]),([true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,true,false,true,true,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true,true,false,true,true,false,true,true] [false,true,true,false,true,true,false,true,true] [true,false,false,true,false,false,true,false,false] 9 local3 n (([true])) (([true,true,false]))

theorem phase4 (n : Nat) : run0 table 10 ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,true,false,true,true,true,true,false])⟩ = some ⟨3,([true,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,true,false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 33 ⟨3,([true,false,true,false,false,true,false,false,true,false,false]) ++ ([true,false,false,true,false,false,true,false,false]) ++ (L),([true,true]) ++ (R)⟩ = some ⟨3,([true,false,true,false,false,true,false,false,true,false,false]) ++ (L),([true,true]) ++ ([true,true,false,true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (33*n) ⟨3,([true,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,true,false])⟩ = some ⟨3,([true,false,true,false,false,true,false,false,true,false,false,true]),([true,true]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [true,false,true,false,false,true,false,false,true,false,false] [true,true] [true,false,false,true,false,false,true,false,false] [true,true,false,true,true,false,true,true,false] 33 local5 n (([true])) (([true,false]))

theorem phase6 (n : Nat) : run0 table 51 ⟨3,([true,false,true,false,false,true,false,false,true,false,false,true]),([true,true]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ = some ⟨2,([false,true]),([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 9 ⟨2,([false]) ++ (L),([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ ([true,true,false,true,true,false,true,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false,true,false,false]) ++ (L),([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (9*n) ⟨2,([false,true]),([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] [true,true,false,true,true,false,true,true,false] [true,false,false,true,false,false,true,false,false] 9 local7 n (([true])) (([true,false]))

theorem phase8 (n : Nat) : run0 table 18 ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false])) ([]) [false,false,true,false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (125+84*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalL n] at H
  rw [show 9+33*n+37+9*n+10+33*n+51+9*n+18=125+84*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 42 (fun n => 125+84*n) entry (by intro n; omega) growth m hm

#print axioms never

end M156

namespace M157

-- 1RB1RC_1RC1LC_0RD0LE_1LD0RA_0LB1LF_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 48 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 9 ⟨1,([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),[]⟩ = some ⟨4,([true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),([true,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 51 ⟨4,([true,false,false,true,false,false,true,false,false,true]) ++ ([false,false,true,false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨4,([true,false,false,true,false,false,true,false,false,true]) ++ (L),([false,true,true,false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (51*n) ⟨4,([true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),([true,true,false])⟩ = some ⟨4,([true,false,false,true,false,false,true,false,false,true]),(rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,false,true,false,false,true,false,false,true] [] [false,false,true,false,false,true,false,false,true] [false,true,true,false,true,true,false,true,true] 51 local1 n ([]) (([true,true,false]))

theorem phase2 (n : Nat) : run0 table 55 ⟨4,([true,false,false,true,false,false,true,false,false,true]),(rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ = some ⟨2,([false,true]),([true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 9 ⟨2,([false]) ++ (L),([true,true,false,true,true,false,true,true,false,true,true]) ++ ([false,true,true,false,true,true,false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false,true,false,false]) ++ (L),([true,true,false,true,true,false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (9*n) ⟨2,([false,true]),([true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,true,false,true,true,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true,true,false,true,true,false,true,true] [false,true,true,false,true,true,false,true,true] [true,false,false,true,false,false,true,false,false] 9 local3 n (([true])) (([true,true,false]))

theorem phase4 (n : Nat) : run0 table 10 ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,true,false,true,true,true,true,false])⟩ = some ⟨3,([true,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,true,false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 51 ⟨3,([true,false,true,false,false,true,false,false,true,false,false]) ++ ([true,false,false,true,false,false,true,false,false]) ++ (L),([true,true]) ++ (R)⟩ = some ⟨3,([true,false,true,false,false,true,false,false,true,false,false]) ++ (L),([true,true]) ++ ([true,true,false,true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (51*n) ⟨3,([true,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,true,false])⟩ = some ⟨3,([true,false,true,false,false,true,false,false,true,false,false,true]),([true,true]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [true,false,true,false,false,true,false,false,true,false,false] [true,true] [true,false,false,true,false,false,true,false,false] [true,true,false,true,true,false,true,true,false] 51 local5 n (([true])) (([true,false]))

theorem phase6 (n : Nat) : run0 table 75 ⟨3,([true,false,true,false,false,true,false,false,true,false,false,true]),([true,true]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ = some ⟨2,([false,true]),([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 9 ⟨2,([false]) ++ (L),([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ ([true,true,false,true,true,false,true,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false,true,false,false]) ++ (L),([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (9*n) ⟨2,([false,true]),([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] [true,true,false,true,true,false,true,true,false] [true,false,false,true,false,false,true,false,false] 9 local7 n (([true])) (([true,false]))

theorem phase8 (n : Nat) : run0 table 18 ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false])) ([]) [false,false,true,false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (167+120*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalL n] at H
  rw [show 9+51*n+55+9*n+10+51*n+75+9*n+18=167+120*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 48 (fun n => 167+120*n) entry (by intro n; omega) growth m hm

#print axioms never

end M157

namespace M158

-- 1RB1RC_1RC1LF_0RD0LE_1LD0RA_0LB1LF_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 10 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),[]⟩ = some ⟨5,(rep [false,false,true,false,false,true,false,false,true] (n)),([true,true,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 9 ⟨5,([false,false,true,false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨5,(L),([true,false,true,true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (9*n) ⟨5,(rep [false,false,true,false,false,true,false,false,true] (n)),([true,true,true,false])⟩ = some ⟨5,[],(rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([true,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [] [] [false,false,true,false,false,true,false,false,true] [true,false,true,true,false,true,true,false,true] 9 local1 n ([]) (([true,true,true,false]))

theorem phase2 (n : Nat) : run0 table 3 ⟨5,[],(rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([true,true,true,false])⟩ = some ⟨2,([false,true]),([true]) ++ (rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([true,true,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 9 ⟨2,([false]) ++ (L),([true]) ++ ([true,false,true,true,false,true,true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false,true,false,false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (9*n) ⟨2,([false,true]),([true]) ++ (rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([true,true,true,false])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true] [true,false,true,true,false,true,true,false,true] [true,false,false,true,false,false,true,false,false] 9 local3 n (([true])) (([true,true,true,false]))

theorem phase4 (n : Nat) : run0 table 5 ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,true,true,false])⟩ = some ⟨5,([false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,false,true,false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 9 ⟨5,([false,false]) ++ ([true,false,false,true,false,false,true,false,false]) ++ (L),(R)⟩ = some ⟨5,([false,false]) ++ (L),([true,false,true,true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (9*n) ⟨5,([false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,false,true,false])⟩ = some ⟨5,([false,false,true]),(rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false] [] [true,false,false,true,false,false,true,false,false] [true,false,true,true,false,true,true,false,true] 9 local5 n (([true])) (([true,false,true,false]))

theorem phase6 (n : Nat) : run0 table 6 ⟨5,([false,false,true]),(rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([true,false,true,false])⟩ = some ⟨2,([false,true]),([true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([true,false,true,false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 9 ⟨2,([false]) ++ (L),([true,true,false,true]) ++ ([true,false,true,true,false,true,true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false,true,false,false]) ++ (L),([true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (9*n) ⟨2,([false,true]),([true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true] (n)) ++ ([true,false,true,false])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true] [true,false,true,true,false,true,true,false,true] [true,false,false,true,false,false,true,false,false] 9 local7 n (([true])) (([true,false,true,false]))

theorem phase8 (n : Nat) : run0 table 9 ⟨2,([false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false,true,false,false])) ([]) [false,false,true,false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (33+36*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalL n] at H
  rw [show 10+9*n+3+9*n+5+9*n+6+9*n+9=33+36*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 33+36*n) entry (by intro n; omega) growth m hm

#print axioms never

end M158

namespace M159

-- 1RB1RC_1RC0LA_0RD0LE_1LD0RA_1LA1LF_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 9 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),[]⟩ = some ⟨4,([true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),([true,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 15 ⟨4,([true]) ++ ([false,false,true,false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨4,([true]) ++ (L),([false,true,true,false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (15*n) ⟨4,([true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),([true,true,false])⟩ = some ⟨4,([true]),(rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true] [] [false,false,true,false,false,true,false,false,true] [false,true,true,false,true,true,false,true,true] 15 local1 n ([]) (([true,true,false]))

theorem phase2 (n : Nat) : run0 table 5 ⟨4,([true]),(rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ = some ⟨0,([true]),([false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 9 ⟨0,([true]) ++ (L),([false,true,true]) ++ ([false,true,true,false,true,true,false,true,true]) ++ (R)⟩ = some ⟨0,([true]) ++ ([false,false,true,false,false,true,false,false,true]) ++ (L),([false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (9*n) ⟨0,([true]),([false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ = some ⟨0,([true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),([false,true,true,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [true] [false,true,true] [false,true,true,false,true,true,false,true,true] [false,false,true,false,false,true,false,false,true] 9 local3 n ([]) (([true,true,false]))

theorem phase4 (n : Nat) : run0 table 3 ⟨0,([true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),([false,true,true,true,true,false])⟩ = some ⟨0,([true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),([true,true,false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 15 ⟨0,([true,false,false,true]) ++ ([false,false,true,false,false,true,false,false,true]) ++ (L),([true]) ++ (R)⟩ = some ⟨0,([true,false,false,true]) ++ (L),([true]) ++ ([true,true,false,true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (15*n) ⟨0,([true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),([true,true,false])⟩ = some ⟨0,([true,false,false,true]),([true]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,false,false,true] [true] [false,false,true,false,false,true,false,false,true] [true,true,false,true,true,false,true,true,false] 15 local5 n ([]) (([true,false]))

theorem phase6 (n : Nat) : run0 table 12 ⟨0,([true,false,false,true]),([true]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ = some ⟨0,([true]),([false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 9 ⟨0,([true]) ++ (L),([false,true,true,false,true,true,false]) ++ ([true,true,false,true,true,false,true,true,false]) ++ (R)⟩ = some ⟨0,([true]) ++ ([false,false,true,false,false,true,false,false,true]) ++ (L),([false,true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (9*n) ⟨0,([true]),([false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ = some ⟨0,([true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),([false,true,true,false,true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [true] [false,true,true,false,true,true,false] [true,true,false,true,true,false,true,true,false] [false,false,true,false,false,true,false,false,true] 9 local7 n ([]) (([true,false]))

theorem phase8 (n : Nat) : run0 table 10 ⟨0,([true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),([false,true,true,false,true,true,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) = ([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (39+48*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 9+15*n+5+9*n+3+15*n+12+9*n+10=39+48*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 39+48*n) entry (by intro n; omega) growth m hm

#print axioms never

end M159

namespace M160

-- 1RB1RC_1RC0RD_0RD0LE_1LD0RA_1LA1LF_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 9 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),[]⟩ = some ⟨4,([true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),([true,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 15 ⟨4,([true]) ++ ([false,false,true,false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨4,([true]) ++ (L),([false,true,true,false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (15*n) ⟨4,([true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)),([true,true,false])⟩ = some ⟨4,([true]),(rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true] [] [false,false,true,false,false,true,false,false,true] [false,true,true,false,true,true,false,true,true] 15 local1 n ([]) (([true,true,false]))

theorem phase2 (n : Nat) : run0 table 5 ⟨4,([true]),(rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ = some ⟨3,([true,false,true]),([true]) ++ (rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 9 ⟨3,([true]) ++ (L),([true]) ++ ([false,true,true,false,true,true,false,true,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,false,false,true,false,false,true,false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (9*n) ⟨3,([true,false,true]),([true]) ++ (rep [false,true,true,false,true,true,false,true,true] (n)) ++ ([true,true,false])⟩ = some ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false,true]),([true,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true] [false,true,true,false,true,true,false,true,true] [false,true,false,false,true,false,false,true,false] 9 local3 n (([false,true])) (([true,true,false]))

theorem phase4 (n : Nat) : run0 table 1 ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false,true]),([true,true,true,false])⟩ = some ⟨0,([true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false,true]),([true,true,false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 15 ⟨0,([true,false]) ++ ([false,true,false,false,true,false,false,true,false]) ++ (L),([true]) ++ (R)⟩ = some ⟨0,([true,false]) ++ (L),([true]) ++ ([true,true,false,true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (15*n) ⟨0,([true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false,true]),([true,true,false])⟩ = some ⟨0,([true,false,false,true]),([true]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,false] [true] [false,true,false,false,true,false,false,true,false] [true,true,false,true,true,false,true,true,false] 15 local5 n (([false,true])) (([true,false]))

theorem phase6 (n : Nat) : run0 table 12 ⟨0,([true,false,false,true]),([true]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ = some ⟨3,([true,false,true]),([true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 9 ⟨3,([true]) ++ (L),([true,false,true,true,false]) ++ ([true,true,false,true,true,false,true,true,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,false,false,true,false,false,true,false]) ++ (L),([true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (9*n) ⟨3,([true,false,true]),([true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false])⟩ = some ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false,true]),([true,false,true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true,false,true,true,false] [true,true,false,true,true,false,true,true,false] [false,true,false,false,true,false,false,true,false] 9 local7 n (([false,true])) (([true,false]))

theorem phase8 (n : Nat) : run0 table 8 ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false,true]),([true,false,true,true,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false,true]) = ([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false,true,false])) (([true])) [true,false,false,true,false,false,true,false] false n
    _ = ([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false,true,false,false])) ([]) [false,false,true,false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (35+48*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalL n] at H
  rw [show 9+15*n+5+9*n+1+15*n+12+9*n+8=35+48*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 35+48*n) entry (by intro n; omega) growth m hm

#print axioms never

end M160

end BB6.Agent11Raw39B1RCPumps
