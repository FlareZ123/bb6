import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B0REPumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M173

-- 1RB0RE_1RC1RF_0RD---_1LD0RA_0LB0LF_1LE1RD

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨true,true,3⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false,false,false,true,true,false,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n)),[]⟩

theorem entry : run0 table 24 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 44 ⟨4,([false,false,false,true,true,false,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n)),[]⟩ = some ⟨5,([false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n)),([true,false,true,true,false,true,false,true,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 8 ⟨5,([false,true]) ++ ([false,true,false,true,false,true,false,true]) ++ (L),(R)⟩ = some ⟨5,([false,true]) ++ (L),([false,true,false,true,false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (8*n) ⟨5,([false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n)),([true,false,true,true,false,true,false,true,true,false])⟩ = some ⟨5,([false,true]),(rep [false,true,false,true,false,true,false,true] (n)) ++ ([true,false,true,true,false,true,false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true] [] [false,true,false,true,false,true,false,true] [false,true,false,true,false,true,false,true] 8 local1 n ([]) (([true,false,true,true,false,true,false,true,true,false]))

theorem phase2 (n : Nat) : run0 table 5 ⟨5,([false,true]),(rep [false,true,false,true,false,true,false,true] (n)) ++ ([true,false,true,true,false,true,false,true,true,false])⟩ = some ⟨2,([false,true]),([true,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) ++ ([true,false,true,true,false,true,false,true,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 56 ⟨2,([false]) ++ (L),([true,false,true]) ++ ([false,true,false,true,false,true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,true,false,true,false,true,false]) ++ (L),([true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (56*n) ⟨2,([false,true]),([true,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) ++ ([true,false,true,true,false,true,false,true,true,false])⟩ = some ⟨2,([false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true,false,true,true,false,true,true,false,true,false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,true] [false,true,false,true,false,true,false,true] [true,false,true,false,true,false,true,false] 56 local3 n (([true])) (([true,false,true,true,false,true,false,true,true,false]))

theorem phase4 (n : Nat) : run0 table 72 ⟨2,([false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true,false,true,true,false,true,true,false,true,false,true,true,false])⟩ = some ⟨4,([false,false,false,true,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,true,true,false,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true]) = ([false,false,false,true,true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) := by
  calc
    _ = ([false,false,false,true,true,false,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,true,true,false,false,true,false,true,false,true,false,true,false])) ([]) [false,true,false,true,false,true,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (121+64*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 44+8*n+5+56*n+72=121+64*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 24 (fun n => 121+64*n) entry (by intro n; omega) growth m hm

#print axioms never

end M173

namespace M175

-- 1RB0RE_1RC0LC_0RD0RA_1LD0RA_1LA0LF_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,[],([true,true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩

theorem entry : run0 table 14 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨0,[],([true,true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩ = some ⟨2,([true]),([false,true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨2,([true]) ++ (L),([false,true,false,true,false]) ++ ([true,false,true,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true,false,false]) ++ (L),([false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨2,([true]),([false,true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩ = some ⟨2,([true]) ++ (rep [true,true,false,false] (n)),([false,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,true,false,true,false] [true,false,true,false] [true,true,false,false] 6 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 18 ⟨2,([true]) ++ (rep [true,true,false,false] (n)),([false,true,false,true,false])⟩ = some ⟨4,([true,false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)),([true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨4,([true,false,false,true,true,false,false]) ++ ([true,true,false,false]) ++ (L),(R)⟩ = some ⟨4,([true,false,false,true,true,false,false]) ++ (L),([true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨4,([true,false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)),([true,false])⟩ = some ⟨4,([true,false,false,true,true,false,false]),(rep [true,false,true,false] (n)) ++ ([true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,false,true,true,false,false] [] [true,true,false,false] [true,false,true,false] 6 local3 n ([]) (([true,false]))

theorem phase4 (n : Nat) : run0 table 9 ⟨4,([true,false,false,true,true,false,false]),(rep [true,false,true,false] (n)) ++ ([true,false])⟩ = some ⟨0,[],([true,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true,false]) = ([true,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) := by
  calc
    _ = ([true,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true,false,true,false,true,false])) (([false])) [false,true,false] true n
    _ = ([true,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true,false,true,false,true,false,true])) ([]) [true,false,true] false n

theorem growth (n : Nat) : run0 table (29+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 2+6*n+18+6*n+9=29+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 14 (fun n => 29+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M175

namespace M178

-- 1RB0RE_1RC0LD_0RD0RA_1LD0RA_1LA0LF_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,[],([true,true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩

theorem entry : run0 table 14 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 3 ⟨0,[],([true,true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩ = some ⟨0,([false,false]),([true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨0,([false]) ++ (L),([true,false,true,false]) ++ ([true,false,true,false]) ++ (R)⟩ = some ⟨0,([false]) ++ ([false,true,true,false]) ++ (L),([true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨0,([false,false]),([true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩ = some ⟨0,([false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [false] [true,false,true,false] [true,false,true,false] [false,true,true,false] 6 local1 n (([false])) ([])

theorem phase2 (n : Nat) : run0 table 17 ⟨0,([false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([true,false,true,false])⟩ = some ⟨4,([true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨4,([true,false,false,true,true,false]) ++ ([false,true,true,false]) ++ (L),(R)⟩ = some ⟨4,([true,false,false,true,true,false]) ++ (L),([true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨4,([true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([true,false])⟩ = some ⟨4,([true,false,false,true,true,false,false]),(rep [true,false,true,false] (n)) ++ ([true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,false,true,true,false] [] [false,true,true,false] [true,false,true,false] 6 local3 n (([false])) (([true,false]))

theorem phase4 (n : Nat) : run0 table 9 ⟨4,([true,false,false,true,true,false,false]),(rep [true,false,true,false] (n)) ++ ([true,false])⟩ = some ⟨0,[],([true,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true,false]) = ([true,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) := by
  calc
    _ = ([true,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true,false,true,false,true,false])) (([false])) [false,true,false] true n
    _ = ([true,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true,false,true,false,true,false,true])) ([]) [true,false,true] false n

theorem growth (n : Nat) : run0 table (29+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 3+6*n+17+6*n+9=29+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 14 (fun n => 29+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M178

namespace M179

-- 1RB0RE_1RC0LD_0RD0RE_1LD0RA_1LA0LF_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,[],([true,true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩

theorem entry : run0 table 14 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨0,[],([true,true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩ = some ⟨1,([true,true]),([true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 10 ⟨1,([true,true]) ++ (L),([true,false,true,false]) ++ ([true,false,true,false]) ++ (R)⟩ = some ⟨1,([true,true]) ++ ([true,true,false,false]) ++ (L),([true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (10*n) ⟨1,([true,true]),([true,false,true,false]) ++ (rep [true,false,true,false] (n))⟩ = some ⟨1,([true,true]) ++ (rep [true,true,false,false] (n)),([true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true,true] [true,false,true,false] [true,false,true,false] [true,true,false,false] 10 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 23 ⟨1,([true,true]) ++ (rep [true,true,false,false] (n)),([true,false,true,false])⟩ = some ⟨4,([true,false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)),([true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨4,([true,false,false,true,true,false,false]) ++ ([true,true,false,false]) ++ (L),(R)⟩ = some ⟨4,([true,false,false,true,true,false,false]) ++ (L),([true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨4,([true,false,false,true,true,false,false]) ++ (rep [true,true,false,false] (n)),([true,false])⟩ = some ⟨4,([true,false,false,true,true,false,false]),(rep [true,false,true,false] (n)) ++ ([true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,false,true,true,false,false] [] [true,true,false,false] [true,false,true,false] 6 local3 n ([]) (([true,false]))

theorem phase4 (n : Nat) : run0 table 9 ⟨4,([true,false,false,true,true,false,false]),(rep [true,false,true,false] (n)) ++ ([true,false])⟩ = some ⟨0,[],([true,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true,false]) = ([true,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) := by
  calc
    _ = ([true,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true,false,true,false,true,false])) (([false])) [false,true,false] true n
    _ = ([true,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true,false,true,false,true,false,true])) ([]) [true,false,true] false n

theorem growth (n : Nat) : run0 table (33+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 1+10*n+23+6*n+9=33+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 14 (fun n => 33+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M179

namespace M199

-- 1RB0RE_1RC1LF_0RD---_1LD0RA_1RB0LF_1LE0LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨5,([false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 10 ⟨5,([false,false,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨5,([false,false,true]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (10*n) ⟨5,([false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),([false])⟩ = some ⟨5,([false,false,true]),(rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,true] [] [false,false,true,false,false,true] [true,false,true,true,false,true] 10 local1 n ([]) (([false]))

theorem phase2 (n : Nat) : run0 table 10 ⟨5,([false,false,true]),(rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ = some ⟨2,([false,true]),([true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 14 ⟨2,([false]) ++ (L),([true,true,false,true]) ++ ([true,false,true,true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (14*n) ⟨2,([false,true]),([true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([false])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true] [true,false,true,true,false,true] [true,false,false,true,false,false] 14 local3 n (([true])) (([false]))

theorem phase4 (n : Nat) : run0 table 10 ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,true,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false])) ([]) [false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (27+24*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 7+10*n+10+14*n+10=27+24*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 27+24*n) entry (by intro n; omega) growth m hm

#print axioms never

end M199

namespace M207

-- 1RB0RE_1RC---_0RD1RE_1LD0RA_0RB0LF_1LF0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,([false,false,true]) ++ (rep [false,false] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 3 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 5 ⟨3,([false,false,true]) ++ (rep [false,false] (n)) ++ ([true]),[]⟩ = some ⟨5,([false,false]) ++ (rep [false,false] (n)) ++ ([true]),([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨5,([false,false]) ++ ([false,false]) ++ (L),(R)⟩ = some ⟨5,([false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨5,([false,false]) ++ (rep [false,false] (n)) ++ ([true]),([false])⟩ = some ⟨5,([false,false,true]),(rep [true,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false] [] [false,false] [true,true] 2 local1 n (([true])) (([false]))

theorem phase2 (n : Nat) : run0 table 4 ⟨5,([false,false,true]),(rep [true,true] (n)) ++ ([false])⟩ = some ⟨1,([false,true]),([true,true]) ++ (rep [true,true] (n)) ++ ([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨1,([false]) ++ (L),([true,true]) ++ ([true,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨1,([false,true]),([true,true]) ++ (rep [true,true] (n)) ++ ([false])⟩ = some ⟨1,([false]) ++ (rep [false,false] (n)) ++ ([true]),([true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,true] [true,true] [false,false] 6 local3 n (([true])) (([false]))

theorem phase4 (n : Nat) : run0 table 8 ⟨1,([false]) ++ (rep [false,false] (n)) ++ ([true]),([true,true,false])⟩ = some ⟨3,([false,false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true]) = ([false,false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (17+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 5+2*n+4+6*n+8=17+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 3 (fun n => 17+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M207

namespace M208

-- 1RB0RE_1RC---_0RD1RF_1LD0RA_0LB0LF_1LF0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true,false,false,true,true,false,false,true,true,true]) ++ (rep [false,true,false,true,true,true,false,true,true,true] (n)),[]⟩

theorem entry : run0 table 111 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 274 ⟨1,([false,true,false,false,true,true,false,false,true,true,true]) ++ (rep [false,true,false,true,true,true,false,true,true,true] (n)),[]⟩ = some ⟨1,([false,true,false,false,true,true,false,false,true,true,true,false,true,false,true,true,true,false,true,true,true]) ++ (rep [false,true,false,true,true,true,false,true,true,true] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,true,false,false,true,true,true,false,true,false,true,true,true,false,true,true,true]) ++ (rep [false,true,false,true,true,true,false,true,true,true] (n)) = ([false,true,false,false,true,true,false,false,true,true,true,false,true,false,true,true,true,false,true,true,true]) ++ (rep [false,true,false,true,true,true,false,true,true,true] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (274+0*n) (family n) = some (family (n+1)) := by
  have H := (phase0 n)
  rw [show 274=274+0*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 111 (fun n => 274+0*n) entry (by intro n; omega) growth m hm

#print axioms never

end M208

namespace M299

-- 1RB0RE_1RC1RC_0RD0LA_1LD0RA_0RF0RC_---0RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [false,false,false] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 8 ⟨1,([false]) ++ (rep [false,false,false] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ = some ⟨3,([false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨3,([false,false,false,false,false]) ++ ([false,false,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,false,false]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨3,([false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ = some ⟨3,([false,false,false,false,false,true]) ++ (rep [false,false] (n)),(rep [true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,false,false] [] [false,false,false] [true,true,true] 3 local1 n (([true]) ++ (rep [false,false] (n))) ([])

theorem phase2 (n : Nat) : run0 table 11 ⟨3,([false,false,false,false,false,true]) ++ (rep [false,false] (n)),(rep [true,true,true] (n))⟩ = some ⟨2,([true,true,true,false,false]) ++ (rep [false,false] (n)),([true]) ++ (rep [true,true,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 5 ⟨2,([true,true]) ++ (L),([true]) ++ ([true,true,true]) ++ (R)⟩ = some ⟨2,([true,true]) ++ ([false,false,false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (5*n) ⟨2,([true,true,true,false,false]) ++ (rep [false,false] (n)),([true]) ++ (rep [true,true,true] (n))⟩ = some ⟨2,([true,true]) ++ (rep [false,false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true,true] [true] [true,true,true] [false,false,false] 5 local3 n (([true,false,false]) ++ (rep [false,false] (n))) ([])

theorem phase4 (n : Nat) : run0 table 4 ⟨2,([true,true]) ++ (rep [false,false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),([true])⟩ = some ⟨1,([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)) = ([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (23+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 8+3*n+11+5*n+4=23+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 23+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M299

namespace M310

-- 1RB0RE_1RC---_0RD0LA_1LD0RA_0RF0RC_---1RC

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨true,true,2⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true]) ++ (rep [false,false] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩

theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨2,([false,true]) ++ (rep [false,false] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ = some ⟨3,([false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨3,([false,false,false,false,false]) ++ ([false,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨3,([false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]) ++ (rep [false,false] (n)),[]⟩ = some ⟨3,([false,false,false,false,false,true]) ++ (rep [false,false] (n)),(rep [true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,false,false] [] [false,false] [true,true] 2 local1 n (([true]) ++ (rep [false,false] (n))) ([])

theorem phase2 (n : Nat) : run0 table 11 ⟨3,([false,false,false,false,false,true]) ++ (rep [false,false] (n)),(rep [true,true] (n))⟩ = some ⟨2,([true,true,true,false,false]) ++ (rep [false,false] (n)),([true]) ++ (rep [true,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 4 ⟨2,([true,true]) ++ (L),([true]) ++ ([true,true]) ++ (R)⟩ = some ⟨2,([true,true]) ++ ([false,false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (4*n) ⟨2,([true,true,true,false,false]) ++ (rep [false,false] (n)),([true]) ++ (rep [true,true] (n))⟩ = some ⟨2,([true,true]) ++ (rep [false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true,true] [true] [true,true] [false,false] 4 local3 n (([true,false,false]) ++ (rep [false,false] (n))) ([])

theorem phase4 (n : Nat) : run0 table 4 ⟨2,([true,true]) ++ (rep [false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),([true])⟩ = some ⟨2,([false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)) = ([false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false]) ++ (rep [false,false] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (22+6*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 7+2*n+11+4*n+4=22+6*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 22+6*n) entry (by intro n; omega) growth m hm

#print axioms never

end M310

namespace M313

-- 1RB0RE_1RC0RF_0RD0LA_1LD0RA_1LA0RC_---0RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [false,false] (n)) ++ ([true]) ++ (rep [true,false,false] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 8 ⟨1,([false]) ++ (rep [false,false] (n)) ++ ([true]) ++ (rep [true,false,false] (n)),[]⟩ = some ⟨3,([false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]) ++ (rep [true,false,false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨3,([false,false,false,false,false]) ++ ([false,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨3,([false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]) ++ (rep [true,false,false] (n)),[]⟩ = some ⟨3,([false,false,false,false,false,true]) ++ (rep [true,false,false] (n)),(rep [true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,false,false] [] [false,false] [true,true] 2 local1 n (([true]) ++ (rep [true,false,false] (n))) ([])

theorem phase2 (n : Nat) : run0 table 15 ⟨3,([false,false,false,false,false,true]) ++ (rep [true,false,false] (n)),(rep [true,true] (n))⟩ = some ⟨1,([true,true,true,false,false]) ++ (rep [true,false,false] (n)),([true]) ++ (rep [true,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 2 ⟨1,([true]) ++ (L),([true]) ++ ([true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([false,false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (2*n) ⟨1,([true,true,true,false,false]) ++ (rep [true,false,false] (n)),([true]) ++ (rep [true,true] (n))⟩ = some ⟨1,([true]) ++ (rep [false,false] (n)) ++ ([true,true,false,false]) ++ (rep [true,false,false] (n)),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true] [true,true] [false,false] 2 local3 n (([true,true,false,false]) ++ (rep [true,false,false] (n))) ([])

theorem phase4 (n : Nat) : run0 table 2 ⟨1,([true]) ++ (rep [false,false] (n)) ++ ([true,true,false,false]) ++ (rep [true,false,false] (n)),([true])⟩ = some ⟨1,([false,false,false]) ++ (rep [false,false] (n)) ++ ([true,true,false,false]) ++ (rep [true,false,false] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false]) ++ (rep [false,false] (n)) ++ ([true,true,false,false]) ++ (rep [true,false,false] (n)) = ([false,false,false]) ++ (rep [false,false] (n)) ++ ([true,true,false,false]) ++ (rep [true,false,false] (n)) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (25+4*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 8+2*n+15+2*n+2=25+4*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 25+4*n) entry (by intro n; omega) growth m hm

#print axioms never

end M313

end BB6.Agent11Raw39B0REPumps
