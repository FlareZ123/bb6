import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39Pumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M2287

-- 1RB1RB_1RC1RE_0RD---_1LD0RA_0LF0RF_0LB1LE

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
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,([false,false,true]) ++ (rep [true,true,false] (n)) ++ ([true,true,false,true,true,false]),[]⟩

theorem entry : run0 table 39 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 5 ⟨3,([false,false,true]) ++ (rep [true,true,false] (n)) ++ ([true,true,false,true,true,false]),[]⟩ = some ⟨4,([false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true,true,false,true,true,false]),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 7 ⟨4,([false,true,true,false]) ++ ([true,true,false]) ++ (L),(R)⟩ = some ⟨4,([false,true,true,false]) ++ (L),([false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (7*n) ⟨4,([false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true,true,false,true,true,false]),[]⟩ = some ⟨4,([false,true,true,false,true,true,false,true,true,false]),(rep [false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true,false] [] [true,true,false] [false,true,false] 7 local1 n (([true,true,false,true,true,false])) ([])

theorem phase2 (n : Nat) : run0 table 21 ⟨4,([false,true,true,false,true,true,false,true,true,false]),(rep [false,true,false] (n))⟩ = some ⟨2,([false,true]),([false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 9 ⟨2,([false,true]) ++ (L),([false,true,false,false,true,false,false,true,false]) ++ ([false,true,false]) ++ (R)⟩ = some ⟨2,([false,true]) ++ ([true,true,false]) ++ (L),([false,true,false,false,true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (9*n) ⟨2,([false,true]),([false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false] (n))⟩ = some ⟨2,([false,true]) ++ (rep [true,true,false] (n)),([false,true,false,false,true,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false,true] [false,true,false,false,true,false,false,true,false] [false,true,false] [true,true,false] 9 local3 n ([]) ([])

theorem phase4 (n : Nat) : run0 table 28 ⟨2,([false,true]) ++ (rep [true,true,false] (n)),([false,true,false,false,true,false,false,true,false])⟩ = some ⟨3,([false,false,true,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) = ([false,false,true,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true,true,false,true,true,false]) := by
  calc
    _ = ([false,false,true,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,true,true,false,true,true,false,true,true])) ([]) [true,true] false n
    _ = ([false,false,true,true,true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,true,true,false,true,true,false,true])) (([false])) [false,true] true n
    _ = ([false,false,true,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,true,true,false,true,true,false])) (([true,false])) [true,false] true n
    _ = ([false,false,true,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,true,true,false,true,true])) (([true,true,false])) [true,true] false n
    _ = ([false,false,true,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,true,true,false,true])) (([false,true,true,false])) [false,true] true n
    _ = ([false,false,true,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true,true,false,true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,true,true,false])) (([true,false,true,true,false])) [true,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (54+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 5+7*n+21+9*n+28=54+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 39 (fun n => 54+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2287

namespace M2357

-- 1RB1RB_1RC1RE_0RD0RF_1LD0RA_1LB1LE_---0LD

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true]) ++ (rep [true,false,true,false] (n)) ++ ([true,false,true,false,true,false]),[]⟩

theorem entry : run0 table 37 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 9 ⟨2,([false,true]) ++ (rep [true,false,true,false] (n)) ++ ([true,false,true,false,true,false]),[]⟩ = some ⟨4,([true,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true,false,true,false,true,false]),([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 8 ⟨4,([true,true,false]) ++ ([true,false,true,false]) ++ (L),(R)⟩ = some ⟨4,([true,true,false]) ++ (L),([true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (8*n) ⟨4,([true,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true,false,true,false,true,false]),([true])⟩ = some ⟨4,([true,true,false,true,false,true,false,true,false]),(rep [true,true,true,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,true,false] [] [true,false,true,false] [true,true,true,true] 8 local1 n (([true,false,true,false,true,false])) (([true]))

theorem phase2 (n : Nat) : run0 table 16 ⟨4,([true,true,false,true,false,true,false,true,false]),(rep [true,true,true,true] (n)) ++ ([true])⟩ = some ⟨2,([true,true]),([true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 12 ⟨2,([true,true]) ++ (L),([true,true,true,true,true,true,true,true]) ++ ([true,true,true,true]) ++ (R)⟩ = some ⟨2,([true,true]) ++ ([true,false,true,false]) ++ (L),([true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (12*n) ⟨2,([true,true]),([true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true])⟩ = some ⟨2,([true,true]) ++ (rep [true,false,true,false] (n)),([true,true,true,true,true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true,true] [true,true,true,true,true,true,true,true] [true,true,true,true] [true,false,true,false] 12 local3 n ([]) (([true]))

theorem phase4 (n : Nat) : run0 table 30 ⟨2,([true,true]) ++ (rep [true,false,true,false] (n)),([true,true,true,true,true,true,true,true,true])⟩ = some ⟨2,([false,true,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) = ([false,true,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true,false,true,false,true,false]) := by
  calc
    _ = ([false,true,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,false,true,false,true,false,true])) ([]) [true,false,true] false n
    _ = ([false,true,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,false,true,false,true,false])) (([false])) [false,true,false] true n
    _ = ([false,true,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([false,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,false,true,false,true])) (([true,false])) [true,false,true] false n
    _ = ([false,true,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true,false,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,false,true,false])) (([false,true,false])) [false,true,false] true n
    _ = ([false,true,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([false,true,false,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,false,true])) (([true,false,true,false])) [true,false,true] false n
    _ = ([false,true,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true,false,true,false,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,false])) (([false,true,false,true,false])) [false,true,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (55+20*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 9+8*n+16+12*n+30=55+20*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 37 (fun n => 55+20*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2357

namespace M2373

-- 1RB1RB_1RC1RE_0RD1LF_1LD0RA_1LC0RB_---0LD

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨1,([false]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ = some ⟨4,([false,true,true,false]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 8 ⟨4,([false,true,true,false]) ++ ([false,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (8*n) ⟨4,([false,true,true,false]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ = some ⟨4,([false,true,true,false,true]) ++ (rep [false,false] (n)),(rep [true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true,false] [] [false,true] [true,true] 8 local1 n (([true]) ++ (rep [false,false] (n))) ([])

theorem phase2 (n : Nat) : run0 table 11 ⟨4,([false,true,true,false,true]) ++ (rep [false,false] (n)),(rep [true,true] (n))⟩ = some ⟨1,([true,true,false,false]) ++ (rep [false,false] (n)),([true]) ++ (rep [true,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 2 ⟨1,([true]) ++ (L),([true]) ++ ([true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([false,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (2*n) ⟨1,([true,true,false,false]) ++ (rep [false,false] (n)),([true]) ++ (rep [true,true] (n))⟩ = some ⟨1,([true]) ++ (rep [false,true] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true] [true,true] [false,true] 2 local3 n (([true,false,false]) ++ (rep [false,false] (n))) ([])

theorem phase4 (n : Nat) : run0 table 2 ⟨1,([true]) ++ (rep [false,true] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),([true])⟩ = some ⟨1,([false,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)) = ([false,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (20+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 7+8*n+11+2*n+2=20+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 20+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2373

namespace M2495

-- 1RB1RB_1RC1RF_0RD---_1LD0RA_0LB1LF_0LE0RE

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
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨false,true,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,([false,false,true]) ++ (rep [true,true,false] (n)) ++ ([true,true,false,true,true,false]),[]⟩

theorem entry : run0 table 39 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 5 ⟨3,([false,false,true]) ++ (rep [true,true,false] (n)) ++ ([true,true,false,true,true,false]),[]⟩ = some ⟨5,([false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true,true,false,true,true,false]),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 7 ⟨5,([false,true,true,false]) ++ ([true,true,false]) ++ (L),(R)⟩ = some ⟨5,([false,true,true,false]) ++ (L),([false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (7*n) ⟨5,([false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true,true,false,true,true,false]),[]⟩ = some ⟨5,([false,true,true,false,true,true,false,true,true,false]),(rep [false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true,true,false] [] [true,true,false] [false,true,false] 7 local1 n (([true,true,false,true,true,false])) ([])

theorem phase2 (n : Nat) : run0 table 21 ⟨5,([false,true,true,false,true,true,false,true,true,false]),(rep [false,true,false] (n))⟩ = some ⟨2,([false,true]),([false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 9 ⟨2,([false,true]) ++ (L),([false,true,false,false,true,false,false,true,false]) ++ ([false,true,false]) ++ (R)⟩ = some ⟨2,([false,true]) ++ ([true,true,false]) ++ (L),([false,true,false,false,true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (9*n) ⟨2,([false,true]),([false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false] (n))⟩ = some ⟨2,([false,true]) ++ (rep [true,true,false] (n)),([false,true,false,false,true,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false,true] [false,true,false,false,true,false,false,true,false] [false,true,false] [true,true,false] 9 local3 n ([]) ([])

theorem phase4 (n : Nat) : run0 table 28 ⟨2,([false,true]) ++ (rep [true,true,false] (n)),([false,true,false,false,true,false,false,true,false])⟩ = some ⟨3,([false,false,true,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) = ([false,false,true,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true,true,false,true,true,false]) := by
  calc
    _ = ([false,false,true,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,true,true,false,true,true,false,true,true])) ([]) [true,true] false n
    _ = ([false,false,true,true,true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,true,true,false,true,true,false,true])) (([false])) [false,true] true n
    _ = ([false,false,true,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,true,true,false,true,true,false])) (([true,false])) [true,false] true n
    _ = ([false,false,true,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,true,true,false,true,true])) (([true,true,false])) [true,true] false n
    _ = ([false,false,true,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,true,true,false,true])) (([false,true,true,false])) [false,true] true n
    _ = ([false,false,true,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true,true,false,true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,true,true,false])) (([true,false,true,true,false])) [true,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (54+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 5+7*n+21+9*n+28=54+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 39 (fun n => 54+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2495

namespace M2557

-- 1RB1RB_1RC1RF_0RD0RE_1LD0RA_---0LD_1LB1LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,false,3⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true]) ++ (rep [true,false,true,false] (n)) ++ ([true,false,true,false,true,false]),[]⟩

theorem entry : run0 table 37 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 9 ⟨2,([false,true]) ++ (rep [true,false,true,false] (n)) ++ ([true,false,true,false,true,false]),[]⟩ = some ⟨5,([true,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true,false,true,false,true,false]),([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 8 ⟨5,([true,true,false]) ++ ([true,false,true,false]) ++ (L),(R)⟩ = some ⟨5,([true,true,false]) ++ (L),([true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (8*n) ⟨5,([true,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true,false,true,false,true,false]),([true])⟩ = some ⟨5,([true,true,false,true,false,true,false,true,false]),(rep [true,true,true,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,true,false] [] [true,false,true,false] [true,true,true,true] 8 local1 n (([true,false,true,false,true,false])) (([true]))

theorem phase2 (n : Nat) : run0 table 16 ⟨5,([true,true,false,true,false,true,false,true,false]),(rep [true,true,true,true] (n)) ++ ([true])⟩ = some ⟨2,([true,true]),([true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 12 ⟨2,([true,true]) ++ (L),([true,true,true,true,true,true,true,true]) ++ ([true,true,true,true]) ++ (R)⟩ = some ⟨2,([true,true]) ++ ([true,false,true,false]) ++ (L),([true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (12*n) ⟨2,([true,true]),([true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true])⟩ = some ⟨2,([true,true]) ++ (rep [true,false,true,false] (n)),([true,true,true,true,true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true,true] [true,true,true,true,true,true,true,true] [true,true,true,true] [true,false,true,false] 12 local3 n ([]) (([true]))

theorem phase4 (n : Nat) : run0 table 30 ⟨2,([true,true]) ++ (rep [true,false,true,false] (n)),([true,true,true,true,true,true,true,true,true])⟩ = some ⟨2,([false,true,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) = ([false,true,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true,false,true,false,true,false]) := by
  calc
    _ = ([false,true,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,false,true,false,true,false,true])) ([]) [true,false,true] false n
    _ = ([false,true,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,false,true,false,true,false])) (([false])) [false,true,false] true n
    _ = ([false,true,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([false,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,false,true,false,true])) (([true,false])) [true,false,true] false n
    _ = ([false,true,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true,false,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,false,true,false])) (([false,true,false])) [false,true,false] true n
    _ = ([false,true,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([false,true,false,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,false,true])) (([true,false,true,false])) [true,false,true] false n
    _ = ([false,true,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true,false,true,false,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,false])) (([false,true,false,true,false])) [false,true,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (55+20*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 9+8*n+16+12*n+30=55+20*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 37 (fun n => 55+20*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2557

namespace M2569

-- 1RB1RB_1RC1RF_0RD1LE_1LD0RA_---0LD_1LC0RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,false,3⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨1,([false]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ = some ⟨5,([false,true,true,false]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 8 ⟨5,([false,true,true,false]) ++ ([false,true]) ++ (L),(R)⟩ = some ⟨5,([false,true,true,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (8*n) ⟨5,([false,true,true,false]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ = some ⟨5,([false,true,true,false,true]) ++ (rep [false,false] (n)),(rep [true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true,true,false] [] [false,true] [true,true] 8 local1 n (([true]) ++ (rep [false,false] (n))) ([])

theorem phase2 (n : Nat) : run0 table 11 ⟨5,([false,true,true,false,true]) ++ (rep [false,false] (n)),(rep [true,true] (n))⟩ = some ⟨1,([true,true,false,false]) ++ (rep [false,false] (n)),([true]) ++ (rep [true,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 2 ⟨1,([true]) ++ (L),([true]) ++ ([true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([false,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (2*n) ⟨1,([true,true,false,false]) ++ (rep [false,false] (n)),([true]) ++ (rep [true,true] (n))⟩ = some ⟨1,([true]) ++ (rep [false,true] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true] [true,true] [false,true] 2 local3 n (([true,false,false]) ++ (rep [false,false] (n))) ([])

theorem phase4 (n : Nat) : run0 table 2 ⟨1,([true]) ++ (rep [false,true] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),([true])⟩ = some ⟨1,([false,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)) = ([false,false,true]) ++ (rep [false,true] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (20+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 7+8*n+11+2*n+2=20+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 20+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2569

namespace M82

-- 1RB1RB_1RC0LE_0RD0LA_1LD0RA_---0RF_1LF1LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([true,true,true,true]) ++ (rep [true,true,true] (n))⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨1,[],([true,true,true,true]) ++ (rep [true,true,true] (n))⟩ = some ⟨2,([true,true]),([true,true,true]) ++ (rep [true,true,true] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 9 ⟨2,([true,true]) ++ (L),([true,true,true]) ++ ([true,true,true]) ++ (R)⟩ = some ⟨2,([true,true]) ++ ([true,true,true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (9*n) ⟨2,([true,true]),([true,true,true]) ++ (rep [true,true,true] (n))⟩ = some ⟨2,([true,true]) ++ (rep [true,true,true] (n)),([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true,true] [true,true,true] [true,true,true] [true,true,true] 9 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 20 ⟨2,([true,true]) ++ (rep [true,true,true] (n)),([true,true,true])⟩ = some ⟨5,([false,false,true,true,true,true]) ++ (rep [true,true,true] (n)),([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 5 ⟨5,([false,false,true,true,true,true]) ++ ([true,true,true]) ++ (L),(R)⟩ = some ⟨5,([false,false,true,true,true,true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (5*n) ⟨5,([false,false,true,true,true,true]) ++ (rep [true,true,true] (n)),([true])⟩ = some ⟨5,([false,false,true,true,true,true]),(rep [true,true,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,true,true,true,true] [] [true,true,true] [true,true,true] 5 local3 n ([]) (([true]))

theorem phase4 (n : Nat) : run0 table 8 ⟨5,([false,false,true,true,true,true]),(rep [true,true,true] (n)) ++ ([true])⟩ = some ⟨1,[],([true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]) = ([true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) := by
  calc
    _ = ([true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true,true,true,true,true])) ([]) [true,true] true n

theorem growth (n : Nat) : run0 table (29+14*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 1+9*n+20+5*n+8=29+14*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 29+14*n) entry (by intro n; omega) growth m hm

#print axioms never

end M82

namespace M109

-- 1RB1RB_1RC0LE_0RD---_1LD0RA_1LA1LF_0LB1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false,false,false,true,false,true,false]) ++ (rep [true,false] (n))⟩

theorem entry : run0 table 69 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨4,[],([true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false,false,false,true,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨2,([false,true]),([true,false,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false,false,false,true,false,true,false]) ++ (rep [true,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 14 ⟨2,([false]) ++ (L),([true,false,true,true,true,true]) ++ ([true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true]) ++ (L),([true,false,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (14*n) ⟨2,([false,true]),([true,false,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false,false,false,true,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨2,([false]) ++ (rep [true,true] (n)) ++ ([true]),([true,false,true,true,true,true,false,false,false,true,false,true,false]) ++ (rep [true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,true,true,true,true] [true,true] [true,true] 14 local1 n (([true])) (([false,false,false,true,false,true,false]) ++ (rep [true,false] (n)))

theorem phase2 (n : Nat) : run0 table 44 ⟨2,([false]) ++ (rep [true,true] (n)) ++ ([true]),([true,false,true,true,true,true,false,false,false,true,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨4,([true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true]),([false,false,false,true,false,true,false,true,false]) ++ (rep [true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 2 ⟨4,([true,true,true,true,true]) ++ ([true,true]) ++ (L),(R)⟩ = some ⟨4,([true,true,true,true,true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (2*n) ⟨4,([true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true]),([false,false,false,true,false,true,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨4,([true,true,true,true,true,true]),(rep [true,true] (n)) ++ ([false,false,false,true,false,true,false,true,false]) ++ (rep [true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,true,true,true,true] [] [true,true] [true,true] 2 local3 n (([true])) (([false,false,false,true,false,true,false,true,false]) ++ (rep [true,false] (n)))

theorem phase4 (n : Nat) : run0 table 6 ⟨4,([true,true,true,true,true,true]),(rep [true,true] (n)) ++ ([false,false,false,true,false,true,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨4,[],([true,true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false,false,false,true,false,true,false,true,false]) ++ (rep [true,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false,false,false,true,false,true,false,true,false]) ++ (rep [true,false] (n)) = ([true,true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false,false,false,true,false,true,false,true,false]) ++ (rep [true,false] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (56+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 6+14*n+44+2*n+6=56+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 69 (fun n => 56+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M109

namespace M241

-- 1RB1RB_1RC0LF_0RD0LA_1LD0RA_1LE1LB_---0RE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,4⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,true,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([true,true,true,true]) ++ (rep [true,true,true] (n))⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨1,[],([true,true,true,true]) ++ (rep [true,true,true] (n))⟩ = some ⟨2,([true,true]),([true,true,true]) ++ (rep [true,true,true] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 9 ⟨2,([true,true]) ++ (L),([true,true,true]) ++ ([true,true,true]) ++ (R)⟩ = some ⟨2,([true,true]) ++ ([true,true,true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (9*n) ⟨2,([true,true]),([true,true,true]) ++ (rep [true,true,true] (n))⟩ = some ⟨2,([true,true]) ++ (rep [true,true,true] (n)),([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true,true] [true,true,true] [true,true,true] [true,true,true] 9 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 20 ⟨2,([true,true]) ++ (rep [true,true,true] (n)),([true,true,true])⟩ = some ⟨4,([false,false,true,true,true,true]) ++ (rep [true,true,true] (n)),([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 5 ⟨4,([false,false,true,true,true,true]) ++ ([true,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,false,true,true,true,true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (5*n) ⟨4,([false,false,true,true,true,true]) ++ (rep [true,true,true] (n)),([true])⟩ = some ⟨4,([false,false,true,true,true,true]),(rep [true,true,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,false,true,true,true,true] [] [true,true,true] [true,true,true] 5 local3 n ([]) (([true]))

theorem phase4 (n : Nat) : run0 table 8 ⟨4,([false,false,true,true,true,true]),(rep [true,true,true] (n)) ++ ([true])⟩ = some ⟨1,[],([true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]) = ([true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) := by
  calc
    _ = ([true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true,true,true,true,true])) ([]) [true,true] true n

theorem growth (n : Nat) : run0 table (29+14*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 1+9*n+20+5*n+8=29+14*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 29+14*n) entry (by intro n; omega) growth m hm

#print axioms never

end M241

namespace M277

-- 1RB1RB_1RC0LF_0RD---_1LD0RA_0LB1LF_1LA1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false,false,false,true,false,true,false]) ++ (rep [true,false] (n))⟩

theorem entry : run0 table 69 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨5,[],([true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false,false,false,true,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨2,([false,true]),([true,false,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false,false,false,true,false,true,false]) ++ (rep [true,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 14 ⟨2,([false]) ++ (L),([true,false,true,true,true,true]) ++ ([true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true]) ++ (L),([true,false,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (14*n) ⟨2,([false,true]),([true,false,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false,false,false,true,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨2,([false]) ++ (rep [true,true] (n)) ++ ([true]),([true,false,true,true,true,true,false,false,false,true,false,true,false]) ++ (rep [true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,true,true,true,true] [true,true] [true,true] 14 local1 n (([true])) (([false,false,false,true,false,true,false]) ++ (rep [true,false] (n)))

theorem phase2 (n : Nat) : run0 table 44 ⟨2,([false]) ++ (rep [true,true] (n)) ++ ([true]),([true,false,true,true,true,true,false,false,false,true,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨5,([true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true]),([false,false,false,true,false,true,false,true,false]) ++ (rep [true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 2 ⟨5,([true,true,true,true,true]) ++ ([true,true]) ++ (L),(R)⟩ = some ⟨5,([true,true,true,true,true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (2*n) ⟨5,([true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true]),([false,false,false,true,false,true,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨5,([true,true,true,true,true,true]),(rep [true,true] (n)) ++ ([false,false,false,true,false,true,false,true,false]) ++ (rep [true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,true,true,true,true] [] [true,true] [true,true] 2 local3 n (([true])) (([false,false,false,true,false,true,false,true,false]) ++ (rep [true,false] (n)))

theorem phase4 (n : Nat) : run0 table 6 ⟨5,([true,true,true,true,true,true]),(rep [true,true] (n)) ++ ([false,false,false,true,false,true,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨5,[],([true,true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false,false,false,true,false,true,false,true,false]) ++ (rep [true,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false,false,false,true,false,true,false,true,false]) ++ (rep [true,false] (n)) = ([true,true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false,false,false,true,false,true,false,true,false]) ++ (rep [true,false] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (56+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 6+14*n+44+2*n+6=56+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 69 (fun n => 56+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M277

end BB6.Agent11Raw39Pumps
