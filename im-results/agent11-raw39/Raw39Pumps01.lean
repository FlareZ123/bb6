import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39Pumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M149

-- 1RB1RB_1RC0LE_0RD---_1LD0RA_1LA1LF_1RE0LB

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
  | 5,false => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [true,false,false,true] (n)) ++ ([true,false,false,true,true,false,false,true]),[]⟩

theorem entry : run0 table 28 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 9 ⟨1,([false]) ++ (rep [true,false,false,true] (n)) ++ ([true,false,false,true,true,false,false,true]),[]⟩ = some ⟨4,([true,true]) ++ (rep [true,false,false,true] (n)) ++ ([true,false,false,true,true,false,false,true]),([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨4,([true,true]) ++ ([true,false,false,true]) ++ (L),(R)⟩ = some ⟨4,([true,true]) ++ (L),([false,false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨4,([true,true]) ++ (rep [true,false,false,true] (n)) ++ ([true,false,false,true,true,false,false,true]),([false])⟩ = some ⟨4,([true,true,true,false,false,true,true,false,false,true]),(rep [false,false,false,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,true] [] [true,false,false,true] [false,false,false,true] 6 local1 n (([true,false,false,true,true,false,false,true])) (([false]))

theorem phase2 (n : Nat) : run0 table 15 ⟨4,([true,true,true,false,false,true,true,false,false,true]),(rep [false,false,false,true] (n)) ++ ([false])⟩ = some ⟨2,([false,true]),([true,false,false,false,true,false,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([false])⟩ := by rfl

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

end M149

namespace M210

-- 1RB1RB_1RC0LF_0RD0LD_1LD0RA_1LF---_0LA0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,([false,false,true]) ++ (rep [true,false,true,false] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 3 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 5 ⟨3,([false,false,true]) ++ (rep [true,false,true,false] (n)) ++ ([true]),[]⟩ = some ⟨5,([true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨5,([true,false]) ++ ([true,false,true,false]) ++ (L),(R)⟩ = some ⟨5,([true,false]) ++ (L),([true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨5,([true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false])⟩ = some ⟨5,([true,false,true]),(rep [true,false,true,false] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,false] [] [true,false,true,false] [true,false,true,false] 4 local1 n (([true])) (([false]))

theorem phase2 (n : Nat) : run0 table 6 ⟨5,([true,false,true]),(rep [true,false,true,false] (n)) ++ ([false])⟩ = some ⟨1,([false,true]),([true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 8 ⟨1,([false]) ++ (L),([true,false,true,false]) ++ ([true,false,true,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,false,true,false]) ++ (L),([true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (8*n) ⟨1,([false,true]),([true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([false])⟩ = some ⟨1,([false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([true,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,false,true,false] [true,false,true,false] [true,false,true,false] 8 local3 n (([true])) (([false]))

theorem phase4 (n : Nat) : run0 table 10 ⟨1,([false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([true,false,true,false,false])⟩ = some ⟨3,([false,false,true,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]) = ([false,false,true,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (21+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 5+4*n+6+8*n+10=21+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 3 (fun n => 21+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M210

namespace M221

-- 1RB1RB_1RC0LF_0RD1LC_1LD0RA_1LF---_1RA0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true,true,false,false]) ++ (rep [true,true,true] (n)) ++ ([true,true,true]),[]⟩

theorem entry : run0 table 32 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 13 ⟨2,([false,true,true,false,false]) ++ (rep [true,true,true] (n)) ++ ([true,true,true]),[]⟩ = some ⟨2,([true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true]),([false,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨2,([true,true,true,true]) ++ ([true,true,true]) ++ (L),(R)⟩ = some ⟨2,([true,true,true,true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨2,([true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true]),([false,false])⟩ = some ⟨2,([true,true,true,true,true,true,true]),(rep [true,true,true] (n)) ++ ([false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 2 [true,true,true,true] [] [true,true,true] [true,true,true] 3 local1 n (([true,true,true])) (([false,false]))

theorem phase2 (n : Nat) : run0 table 8 ⟨2,([true,true,true,true,true,true,true]),(rep [true,true,true] (n)) ++ ([false,false])⟩ = some ⟨3,([true,false]),([true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 9 ⟨3,([true,false]) ++ (L),([true,true,true,true,true,true]) ++ ([true,true,true]) ++ (R)⟩ = some ⟨3,([true,false]) ++ ([true,true,true]) ++ (L),([true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (9*n) ⟨3,([true,false]),([true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false,false])⟩ = some ⟨3,([true,false]) ++ (rep [true,true,true] (n)),([true,true,true,true,true,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true,false] [true,true,true,true,true,true] [true,true,true] [true,true,true] 9 local3 n ([]) (([false,false]))

theorem phase4 (n : Nat) : run0 table 21 ⟨3,([true,false]) ++ (rep [true,true,true] (n)),([true,true,true,true,true,true,false,false])⟩ = some ⟨2,([false,true,true,false,false,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,false,false,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) = ([false,true,true,false,false,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true]) := by
  calc
    _ = ([false,true,true,false,false,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,false,true,true,true,true,true])) ([]) [true,true] true n
    _ = ([false,true,true,false,false,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,false,true,true,true,true])) (([true])) [true,true] true n
    _ = ([false,true,true,false,false,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,false,true,true,true])) (([true,true])) [true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (42+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 13+3*n+8+9*n+21=42+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 32 (fun n => 42+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M221

namespace M238

-- 1RB1RB_1RC0LF_0RD0LE_1LD0RA_1LA---_1LC0LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],(rep [false,false,false,true] (n)) ++ ([false,false,false,true,false,false])⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨5,[],(rep [false,false,false,true] (n)) ++ ([false,false,false,true,false,false])⟩ = some ⟨3,([true,false]),(rep [false,false,false,true] (n)) ++ ([false,false,false,true,false,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨3,([true]) ++ (L),([false,false,false,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,false]) ++ (L),(R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨3,([true,false]),(rep [false,false,false,true] (n)) ++ ([false,false,false,true,false,false])⟩ = some ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [] [false,false,false,true] [false,true,true,false] 4 local1 n (([false])) (([false,false,false,true,false,false]))

theorem phase2 (n : Nat) : run0 table 8 ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 20 ⟨3,([false,false,true,true,false,false,true,true,false]) ++ ([false,true,true,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (L),([false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (20*n) ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true,false,false,true,true,false] [] [false,true,true,false] [false,true,false,false] 20 local3 n (([false])) ([])

theorem phase4 (n : Nat) : run0 table 32 ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ = some ⟨5,[],([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) = ([false,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([false,false,false,true,false,false]) := by
  calc
    _ = ([false,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false] (n)) ++ ([false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,true,false,false,false,true,false])) ([]) [false,true,false] false n
    _ = ([false,false,false,true,false,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,true,false,false,false,true])) (([false])) [false,false,true] false n
    _ = ([false,false,false,true,false,false,false]) ++ (rep [true,false,false,false] (n)) ++ ([true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,true,false,false,false])) (([false,false])) [false,false,false] true n
    _ = ([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) ++ ([false,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,true,false,false])) (([true,false,false])) [true,false,false] false n
    _ = ([false,false,false,true,false]) ++ (rep [false,false,true,false] (n)) ++ ([false,false,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,true,false])) (([false,true,false,false])) [false,true,false] false n
    _ = ([false,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([false,false,false,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,true])) (([false,false,true,false,false])) [false,false,true] false n

theorem growth (n : Nat) : run0 table (42+24*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 2+4*n+8+20*n+32=42+24*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 15 (fun n => 42+24*n) entry (by intro n; omega) growth m hm

#print axioms never

end M238

namespace M259

-- 1RB1RB_1RC0LF_0RD0RB_1LD0RA_0LD---_1LE0RF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,3⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,true,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨1,([false]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ = some ⟨3,([false,false,true]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 8 ⟨3,([false,false,true]) ++ ([false,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true]) ++ (L),([false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (8*n) ⟨3,([false,false,true]) ++ (rep [false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ = some ⟨3,([false,false,true,true]) ++ (rep [false] (n)),(rep [false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true] [] [false,true] [false,true] 8 local1 n (([true]) ++ (rep [false] (n))) ([])

theorem phase2 (n : Nat) : run0 table 11 ⟨3,([false,false,true,true]) ++ (rep [false] (n)),(rep [false,true] (n))⟩ = some ⟨1,([false,true,false]) ++ (rep [false] (n)),([true]) ++ (rep [false,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 2 ⟨1,([false]) ++ (L),([true]) ++ ([false,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (2*n) ⟨1,([false,true,false]) ++ (rep [false] (n)),([true]) ++ (rep [false,true] (n))⟩ = some ⟨1,([false]) ++ (rep [false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true] [false,true] [false,true] 2 local3 n (([true,false]) ++ (rep [false] (n))) ([])

theorem phase4 (n : Nat) : run0 table 2 ⟨1,([false]) ++ (rep [false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)),([true])⟩ = some ⟨1,([false,false,true]) ++ (rep [false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true]) ++ (rep [false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)) = ([false,false,true]) ++ (rep [false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (15+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 2+8*n+11+2*n+2=15+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 15+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M259

namespace M275

-- 1RB1RB_1RC0LF_0RD---_1LD0RA_0LB0LB_1LA1LE

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
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [true,false,false,true] (n)) ++ ([true,false,false,true,true,false,false,true]),[]⟩

theorem entry : run0 table 24 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 9 ⟨1,([false]) ++ (rep [true,false,false,true] (n)) ++ ([true,false,false,true,true,false,false,true]),[]⟩ = some ⟨1,(rep [true,false,false,true] (n)) ++ ([true,false,false,true,true,false,false,true]),([false,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨1,([true,false,false,true]) ++ (L),(R)⟩ = some ⟨1,(L),([false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨1,(rep [true,false,false,true] (n)) ++ ([true,false,false,true,true,false,false,true]),([false,true,false])⟩ = some ⟨1,([true,false,false,true,true,false,false,true]),(rep [false,true,false,false] (n)) ++ ([false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [] [] [true,false,false,true] [false,true,false,false] 6 local1 n (([true,false,false,true,true,false,false,true])) (([false,true,false]))

theorem phase2 (n : Nat) : run0 table 13 ⟨1,([true,false,false,true,true,false,false,true]),(rep [false,true,false,false] (n)) ++ ([false,true,false])⟩ = some ⟨2,([false,true]),([true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) ++ ([false,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 4 ⟨2,([false]) ++ (L),([true,false,false,false,true,false,false]) ++ ([false,true,false,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false]) ++ (L),([true,false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (4*n) ⟨2,([false,true]),([true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) ++ ([false,true,false])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false] (n)) ++ ([true]),([true,false,false,false,true,false,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,false,true,false,false] [false,true,false,false] [true,true,false,false] 4 local3 n (([true])) (([false,true,false]))

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

theorem growth (n : Nat) : run0 table (33+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 9+6*n+13+4*n+11=33+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 24 (fun n => 33+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M275

namespace M276

-- 1RB1RB_1RC0LF_0RD---_1LD0RA_0LB0RF_1LA1LE

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
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [true,false,false,true] (n)) ++ ([true,false,false,true,true,false,false,true]),[]⟩

theorem entry : run0 table 24 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨1,([false]) ++ (rep [true,false,false,true] (n)) ++ ([true,false,false,true,true,false,false,true]),[]⟩ = some ⟨5,([true,false]) ++ (rep [true,false,false,true] (n)) ++ ([true,false,false,true,true,false,false,true]),([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 8 ⟨5,([true,false]) ++ ([true,false,false,true]) ++ (L),(R)⟩ = some ⟨5,([true,false]) ++ (L),([false,false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (8*n) ⟨5,([true,false]) ++ (rep [true,false,false,true] (n)) ++ ([true,false,false,true,true,false,false,true]),([false])⟩ = some ⟨5,([true,false,true,false,false,true,true,false,false,true]),(rep [false,false,false,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,false] [] [true,false,false,true] [false,false,false,true] 8 local1 n (([true,false,false,true,true,false,false,true])) (([false]))

theorem phase2 (n : Nat) : run0 table 19 ⟨5,([true,false,true,false,false,true,true,false,false,true]),(rep [false,false,false,true] (n)) ++ ([false])⟩ = some ⟨2,([false,true]),([true,false,false,false,true,false,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([false])⟩ := by rfl

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

theorem growth (n : Nat) : run0 table (37+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 7+8*n+19+4*n+11=37+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 24 (fun n => 37+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M276

namespace M283

-- 1RB1RB_1RC0LF_0RD0LD_1LD0RA_0LF---_1RB1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true]) ++ (rep [true,false,true,false] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨2,([false,true]) ++ (rep [true,false,true,false] (n)) ++ ([true]),[]⟩ = some ⟨5,([true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨5,([true,false]) ++ ([true,false,true,false]) ++ (L),(R)⟩ = some ⟨5,([true,false]) ++ (L),([false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨5,([true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false])⟩ = some ⟨5,([true,false,true]),(rep [false,true,false,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,false] [] [true,false,true,false] [false,true,false,true] 4 local1 n (([true])) (([false]))

theorem phase2 (n : Nat) : run0 table 5 ⟨5,([true,false,true]),(rep [false,true,false,true] (n)) ++ ([false])⟩ = some ⟨1,([false,true]),([true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 8 ⟨1,([false]) ++ (L),([true,false,true]) ++ ([false,true,false,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,false,true,false]) ++ (L),([true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (8*n) ⟨1,([false,true]),([true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([false])⟩ = some ⟨1,([false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,false,true] [false,true,false,true] [true,false,true,false] 8 local3 n (([true])) (([false]))

theorem phase4 (n : Nat) : run0 table 9 ⟨1,([false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([true,false,true,false])⟩ = some ⟨2,([false,true,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]) = ([false,true,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (20+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 6+4*n+5+8*n+9=20+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 20+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M283

namespace M288

-- 1RB1RB_1RC0LF_0RD0RB_1LD0RA_1LB---_1LB1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],(rep [false,true,false,true,false,true,false,true] (n)) ++ ([false,true,false,true,false,true,false,true,true,false,true,false,true,false,false])⟩

theorem entry : run0 table 103 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨5,[],(rep [false,true,false,true,false,true,false,true] (n)) ++ ([false,true,false,true,false,true,false,true,true,false,true,false,true,false,false])⟩ = some ⟨2,([true,true]),(rep [false,true,false,true,false,true,false,true] (n)) ++ ([false,true,false,true,false,true,false,true,true,false,true,false,true,false,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 8 ⟨2,([true]) ++ (L),([false,true,false,true,false,true,false,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,false,true,false,true,false,true,false]) ++ (L),(R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (8*n) ⟨2,([true,true]),(rep [false,true,false,true,false,true,false,true] (n)) ++ ([false,true,false,true,false,true,false,true,true,false,true,false,true,false,false])⟩ = some ⟨2,([true]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,true,true,false,true,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [] [false,true,false,true,false,true,false,true] [true,false,true,false,true,false,true,false] 8 local1 n (([true])) (([false,true,false,true,false,true,false,true,true,false,true,false,true,false,false]))

theorem phase2 (n : Nat) : run0 table 9 ⟨2,([true]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,true,true,false,true,false,true,false,false])⟩ = some ⟨1,([true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 8 ⟨1,([true,false,true,false,true,false,true,false,true,false]) ++ ([true,false,true,false,true,false,true,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,true,false,true,false,true,false,true,false]) ++ (L),([true,false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (8*n) ⟨1,([true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,false])⟩ = some ⟨1,([true,false,true,false,true,false,true,false,true,false,true]),(rep [true,false,true,false,true,false,true,false] (n)) ++ ([false,true,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,true,false,true,false,true,false,true,false] [] [true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false] 8 local3 n (([true])) (([false,true,false,true,false,false]))

theorem phase4 (n : Nat) : run0 table 13 ⟨1,([true,false,true,false,true,false,true,false,true,false,true]),(rep [true,false,true,false,true,false,true,false] (n)) ++ ([false,true,false,true,false,false])⟩ = some ⟨2,([true,true]),([false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([false,true,false,true,false,false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 8 ⟨2,([true]) ++ (L),([false,true,false,true,false,true,false,true,false,true,false]) ++ ([true,false,true,false,true,false,true,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,false,true,false,true,false,true,false]) ++ (L),([false,true,false,true,false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (8*n) ⟨2,([true,true]),([false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([false,true,false,true,false,false])⟩ = some ⟨2,([true]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,true,false,true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false] 8 local5 n (([true])) (([false,true,false,true,false,false]))

theorem phase6 (n : Nat) : run0 table 25 ⟨2,([true]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,false,false])⟩ = some ⟨1,([true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true,true,false,true,false,false,false,false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 8 ⟨1,([true,false,true,false,true,false,true,false,true,false]) ++ ([true,false,true,false,true,false,true,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,true,false,true,false,true,false,true,false]) ++ (L),([true,false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (8*n) ⟨1,([true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true,true,false,true,false,false,false,false])⟩ = some ⟨1,([true,false,true,false,true,false,true,false,true,false,true]),(rep [true,false,true,false,true,false,true,false] (n)) ++ ([true,true,false,true,false,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,true,false,true,false,true,false,true,false] [] [true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false] 8 local7 n (([true])) (([true,true,false,true,false,false,false,false]))

theorem phase8 (n : Nat) : run0 table 13 ⟨1,([true,false,true,false,true,false,true,false,true,false,true]),(rep [true,false,true,false,true,false,true,false] (n)) ++ ([true,true,false,true,false,false,false,false])⟩ = some ⟨2,([true,true]),([false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true,true,false,true,false,false,false,false])⟩ := by rfl

theorem local9 (L R : List Bool) : run0 table 8 ⟨2,([true]) ++ (L),([false,true,false,true,false,true,false,true,false,true,false]) ++ ([true,false,true,false,true,false,true,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,false,true,false,true,false,true,false]) ++ (L),([false,true,false,true,false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase9 (n : Nat) : run0 table (8*n) ⟨2,([true,true]),([false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true,true,false,true,false,false,false,false])⟩ = some ⟨2,([true]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,true,false,true,false,true,true,false,true,false,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,true,false,true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false] 8 local9 n (([true])) (([true,true,false,true,false,false,false,false]))

theorem phase10 (n : Nat) : run0 table 13 ⟨2,([true]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,true,false,true,false,true,true,false,true,false,false,false,false])⟩ = some ⟨1,([true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,false,false,false])⟩ := by rfl

theorem local11 (L R : List Bool) : run0 table 8 ⟨1,([true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ ([true,false,true,false,true,false,true,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (L),([true,false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase11 (n : Nat) : run0 table (8*n) ⟨1,([true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,false,false,false])⟩ = some ⟨1,([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]),(rep [true,false,true,false,true,false,true,false] (n)) ++ ([false,true,false,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,true,false,true,false,true,false,true,false,true,false,true,false] [] [true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false] 8 local11 n (([true])) (([false,true,false,false,false,false]))

theorem phase12 (n : Nat) : run0 table 17 ⟨1,([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]),(rep [true,false,true,false,true,false,true,false] (n)) ++ ([false,true,false,false,false,false])⟩ = some ⟨2,([true,true]),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([false,true,false,false,false,false])⟩ := by rfl

theorem local13 (L R : List Bool) : run0 table 8 ⟨2,([true]) ++ (L),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ ([true,false,true,false,true,false,true,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,false,true,false,true,false,true,false]) ++ (L),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase13 (n : Nat) : run0 table (8*n) ⟨2,([true,true]),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([false,true,false,false,false,false])⟩ = some ⟨2,([true]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false] 8 local13 n (([true])) (([false,true,false,false,false,false]))

theorem phase14 (n : Nat) : run0 table 41 ⟨2,([true]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,false,false,false])⟩ = some ⟨1,([true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true,true,false,true,false,true,false,false])⟩ := by rfl

theorem local15 (L R : List Bool) : run0 table 8 ⟨1,([true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ ([true,false,true,false,true,false,true,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (L),([true,false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase15 (n : Nat) : run0 table (8*n) ⟨1,([true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true,true,false,true,false,true,false,false])⟩ = some ⟨1,([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]),(rep [true,false,true,false,true,false,true,false] (n)) ++ ([true,true,false,true,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,true,false,true,false,true,false,true,false,true,false,true,false] [] [true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false] 8 local15 n (([true])) (([true,true,false,true,false,true,false,false]))

theorem phase16 (n : Nat) : run0 table 15 ⟨1,([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]),(rep [true,false,true,false,true,false,true,false] (n)) ++ ([true,true,false,true,false,true,false,false])⟩ = some ⟨5,[],([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true,true,false,true,false,true,false,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true,true,false,true,false,true,false,false]) = ([false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) ++ ([false,true,false,true,false,true,false,true,true,false,true,false,true,false,false]) := by
  calc
    _ = ([false,true,false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) ++ ([false,true,true,false,true,false,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,false,true,false,true,false,true,false,true,false,true])) (([true,true,false,true,false,true,false,false])) [true,false,true,false,true,false,true] false n
    _ = ([false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true,false,true,true,false,true,false,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,false,true,false,true,false,true,false,true,false])) (([false,true,true,false,true,false,true,false,false])) [false,true,false,true,false,true,false] true n
    _ = ([false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) ++ ([false,true,false,true,true,false,true,false,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,false,true,false,true,false,true,false,true])) (([true,false,true,true,false,true,false,true,false,false])) [true,false,true,false,true,false,true] false n
    _ = ([false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true,false,true,false,true,true,false,true,false,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,false,true,false,true,false,true,false])) (([false,true,false,true,true,false,true,false,true,false,false])) [false,true,false,true,false,true,false] true n
    _ = ([false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) ++ ([false,true,false,true,false,true,true,false,true,false,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,false,true,false,true,false,true])) (([true,false,true,false,true,true,false,true,false,true,false,false])) [true,false,true,false,true,false,true] false n
    _ = ([false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true,false,true,false,true,false,true,true,false,true,false,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,false,true,false,true,false])) (([false,true,false,true,false,true,true,false,true,false,true,false,false])) [false,true,false,true,false,true,false] true n
    _ = ([false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) ++ ([false,true,false,true,false,true,false,true,true,false,true,false,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,false,true,false,true])) (([true,false,true,false,true,false,true,true,false,true,false,true,false,false])) [true,false,true,false,true,false,true] false n

theorem growth (n : Nat) : run0 table (148+64*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n)) (phase9 n)) (phase10 n)) (phase11 n)) (phase12 n)) (phase13 n)) (phase14 n)) (phase15 n)) (phase16 n))
  rw [finalR n] at H
  rw [show 2+8*n+9+8*n+13+8*n+25+8*n+13+8*n+13+8*n+17+8*n+41+8*n+15=148+64*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 103 (fun n => 148+64*n) entry (by intro n; omega) growth m hm

#print axioms never

end M288

namespace M305

-- 1RB1RB_1RC0LF_0RD0RE_1LD0RA_1LF---_0LB1LE

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
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n)) ++ ([true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]),[]⟩

theorem entry : run0 table 81 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 9 ⟨1,([false]) ++ (rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n)) ++ ([true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]),[]⟩ = some ⟨5,(rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n)) ++ ([true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]),([true,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 16 ⟨5,([true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (L),(R)⟩ = some ⟨5,(L),([false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (16*n) ⟨5,(rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n)) ++ ([true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]),([true,true,false])⟩ = some ⟨5,([true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]),(rep [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] (n)) ++ ([true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [] [] [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] 16 local1 n (([true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true])) (([true,true,false]))

theorem phase2 (n : Nat) : run0 table 28 ⟨5,([true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]),(rep [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] (n)) ++ ([true,true,false])⟩ = some ⟨2,([false,true]),([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true]) ++ (rep [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] (n)) ++ ([true,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 16 ⟨2,([false]) ++ (L),([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true]) ++ ([false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (16*n) ⟨2,([false,true]),([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true]) ++ (rep [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] (n)) ++ ([true,true,false])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] 16 local3 n (([true])) (([true,true,false]))

theorem phase4 (n : Nat) : run0 table 19 ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,true,true,false])⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 16 ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ ([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),([false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (16*n) ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false])⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]),(rep [false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false] (n)) ++ ([true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] [] [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] [false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false] 16 local5 n (([true])) (([true,false]))

theorem phase6 (n : Nat) : run0 table 33 ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]),(rep [false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false] (n)) ++ ([true,false])⟩ = some ⟨2,([false,true]),([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false] (n)) ++ ([true,false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 16 ⟨2,([false]) ++ (L),([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false]) ++ ([false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (16*n) ⟨2,([false,true]),([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false] (n)) ++ ([true,false])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false] [false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false] [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] 16 local7 n (([true])) (([true,false]))

theorem phase8 (n : Nat) : run0 table 25 ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,true,false])⟩ = some ⟨4,([false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem local9 (L R : List Bool) : run0 table 16 ⟨4,([false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ ([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),(R)⟩ = some ⟨4,([false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),([true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase9 (n : Nat) : run0 table (16*n) ⟨4,([false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),[]⟩ = some ⟨4,([false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]),(rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] [] [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] 16 local9 n (([true])) ([])

theorem phase10 (n : Nat) : run0 table 39 ⟨4,([false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]),(rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n))⟩ = some ⟨2,([false,true]),([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n))⟩ := by rfl

theorem local11 (L R : List Bool) : run0 table 16 ⟨2,([false]) ++ (L),([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ ([true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase11 (n : Nat) : run0 table (16*n) ⟨2,([false,true]),([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n))⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] 16 local11 n (([true])) ([])

theorem phase12 (n : Nat) : run0 table 31 ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true])⟩ = some ⟨1,([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n)) ++ ([true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) := by
  calc
    _ = ([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false] (n)) ++ ([false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false])) (([true])) [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false] false n
    _ = ([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true]) ++ (rep [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] (n)) ++ ([false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true])) (([false,true])) [false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] false n
    _ = ([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n)) ++ ([true,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true])) (([false,false,true])) [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] true n
    _ = ([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true,true,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false])) (([true,false,false,true])) [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] true n
    _ = ([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false] (n)) ++ ([false,true,true,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false])) (([true,true,false,false,true])) [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false] false n
    _ = ([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true]) ++ (rep [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] (n)) ++ ([false,false,true,true,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true])) (([false,true,true,false,false,true])) [false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] false n
    _ = ([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n)) ++ ([true,false,false,true,true,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true])) (([false,false,true,true,false,false,true])) [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] true n
    _ = ([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true,true,false,false,true,true,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false])) (([true,false,false,true,true,false,false,true])) [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] true n
    _ = ([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false] (n)) ++ ([false,true,true,false,false,true,true,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false])) (([true,true,false,false,true,true,false,false,true])) [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false] false n
    _ = ([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true]) ++ (rep [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] (n)) ++ ([false,false,true,true,false,false,true,true,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true])) (([false,true,true,false,false,true,true,false,false,true])) [false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] false n
    _ = ([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n)) ++ ([true,false,false,true,true,false,false,true,true,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true])) (([false,false,true,true,false,false,true,true,false,false,true])) [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] true n
    _ = ([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true,true,false,false,true,true,false,false,true,true,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false])) (([true,false,false,true,true,false,false,true,true,false,false,true])) [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] true n
    _ = ([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false] (n)) ++ ([false,true,true,false,false,true,true,false,false,true,true,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false])) (([true,true,false,false,true,true,false,false,true,true,false,false,true])) [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false] false n
    _ = ([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true]) ++ (rep [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] (n)) ++ ([false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true])) (([false,true,true,false,false,true,true,false,false,true,true,false,false,true])) [false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] false n
    _ = ([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n)) ++ ([true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true])) (([false,false,true,true,false,false,true,true,false,false,true,true,false,false,true])) [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (184+96*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n)) (phase9 n)) (phase10 n)) (phase11 n)) (phase12 n))
  rw [finalL n] at H
  rw [show 9+16*n+28+16*n+19+16*n+33+16*n+25+16*n+39+16*n+31=184+96*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 81 (fun n => 184+96*n) entry (by intro n; omega) growth m hm

#print axioms never

end M305

end BB6.Agent11Raw39Pumps
