import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B0RBPumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M208

-- 1RB0RB_1RC0LF_0RD1RE_1LD0RA_1LB---_0LE0RA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨false,true,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([true,false,false,true,false,false]) ++ (rep [true,false,false] (n))⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨1,[],([true,false,false,true,false,false]) ++ (rep [true,false,false] (n))⟩ = some ⟨2,([true,true]),([false,false,true,false,false]) ++ (rep [true,false,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 9 ⟨2,([true,true]) ++ (L),([false,false,true,false,false]) ++ ([true,false,false]) ++ (R)⟩ = some ⟨2,([true,true]) ++ ([true,false,false]) ++ (L),([false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (9*n) ⟨2,([true,true]),([false,false,true,false,false]) ++ (rep [true,false,false] (n))⟩ = some ⟨2,([true,true]) ++ (rep [true,false,false] (n)),([false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true,true] [false,false,true,false,false] [true,false,false] [true,false,false] 9 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 23 ⟨2,([true,true]) ++ (rep [true,false,false] (n)),([false,false,true,false,false])⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([true,false,false,true,false,false,true,false,false]) ++ ([true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (L),([true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)),[]⟩ = some ⟨1,([true,false,false,true,false,false,true,false,false]),(rep [true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false,true,false,false,true,false,false] [] [true,false,false] [true,false,false] 3 local3 n ([]) ([])

theorem phase4 (n : Nat) : run0 table 9 ⟨1,([true,false,false,true,false,false,true,false,false]),(rep [true,false,false] (n))⟩ = some ⟨1,[],([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) = ([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (33+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 1+9*n+23+3*n+9=33+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 33+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M208

namespace M211

-- 1RB0RB_1RC0LF_0RD1LB_1LD0RA_1LC---_0LE0LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true,true,false,false,false,false,true,true,false,false]) ++ (rep [false,true,true,false,false] (n)),[]⟩

theorem entry : run0 table 45 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 10 ⟨2,([false,true,true,false,false,false,false,true,true,false,false]) ++ (rep [false,true,true,false,false] (n)),[]⟩ = some ⟨2,([true,true,false,false,false,true,true,false,false]) ++ (rep [false,true,true,false,false] (n)),([true,false,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 13 ⟨2,([true,true,false,false,false,true,true,false,false]) ++ ([false,true,true,false,false]) ++ (L),(R)⟩ = some ⟨2,([true,true,false,false,false,true,true,false,false]) ++ (L),([true,false,false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (13*n) ⟨2,([true,true,false,false,false,true,true,false,false]) ++ (rep [false,true,true,false,false] (n)),([true,false,false])⟩ = some ⟨2,([true,true,false,false,false,true,true,false,false]),(rep [true,false,false,false,true] (n)) ++ ([true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 2 [true,true,false,false,false,true,true,false,false] [] [false,true,true,false,false] [true,false,false,false,true] 13 local1 n ([]) (([true,false,false]))

theorem phase2 (n : Nat) : run0 table 27 ⟨2,([true,true,false,false,false,true,true,false,false]),(rep [true,false,false,false,true] (n)) ++ ([true,false,false])⟩ = some ⟨3,([true,false]),([false,false,false,true,true,false,false,false,true]) ++ (rep [true,false,false,false,true] (n)) ++ ([true,false,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 25 ⟨3,([true]) ++ (L),([false,false,false,true,true,false,false,false,true]) ++ ([true,false,false,false,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,false,true,true,false]) ++ (L),([false,false,false,true,true,false,false,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (25*n) ⟨3,([true,false]),([false,false,false,true,true,false,false,false,true]) ++ (rep [true,false,false,false,true] (n)) ++ ([true,false,false])⟩ = some ⟨3,([true]) ++ (rep [false,false,true,true,false] (n)) ++ ([false]),([false,false,false,true,true,false,false,false,true,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,false,false,true,true,false,false,false,true] [true,false,false,false,true] [false,false,true,true,false] 25 local3 n (([false])) (([true,false,false]))

theorem phase4 (n : Nat) : run0 table 44 ⟨3,([true]) ++ (rep [false,false,true,true,false] (n)) ++ ([false]),([false,false,false,true,true,false,false,false,true,true,false,false])⟩ = some ⟨2,([false,true,true,false,false,false,false,true,true,false,false,false,true,true,false]) ++ (rep [false,false,true,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,false,false,false,false,true,true,false,false,false,true,true,false]) ++ (rep [false,false,true,true,false] (n)) ++ ([false]) = ([false,true,true,false,false,false,false,true,true,false,false,false,true,true,false,false]) ++ (rep [false,true,true,false,false] (n)) := by
  calc
    _ = ([false,true,true,false,false,false,false,true,true,false,false,false,true,true,false,false]) ++ (rep [false,true,true,false,false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,false,false,false,true,true,false,false,false,true,true,false])) ([]) [false,true,true,false] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (81+38*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 10+13*n+27+25*n+44=81+38*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 45 (fun n => 81+38*n) entry (by intro n; omega) growth m hm

#print axioms never

end M211

namespace M217

-- 1RB0RB_1RC0LF_0RD0RA_1LD0RA_1RF1LB_0LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([true,false,false,true,false,false]) ++ (rep [true,false,false] (n))⟩

theorem entry : run0 table 17 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨1,[],([true,false,false,true,false,false]) ++ (rep [true,false,false] (n))⟩ = some ⟨2,([true,true]),([false,false,true,false,false]) ++ (rep [true,false,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨2,([true]) ++ (L),([false,false,true,false,false]) ++ ([true,false,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true,false]) ++ (L),([false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨2,([true,true]),([false,false,true,false,false]) ++ (rep [true,false,false] (n))⟩ = some ⟨2,([true]) ++ (rep [true,true,false] (n)) ++ ([true]),([false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,false,true,false,false] [true,false,false] [true,true,false] 3 local1 n (([true])) ([])

theorem phase2 (n : Nat) : run0 table 14 ⟨2,([true]) ++ (rep [true,true,false] (n)) ++ ([true]),([false,false,true,false,false])⟩ = some ⟨5,([false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true]),([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨5,([false,true,true,false,true,true,false]) ++ ([true,true,false]) ++ (L),(R)⟩ = some ⟨5,([false,true,true,false,true,true,false]) ++ (L),([false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨5,([false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true]),([false])⟩ = some ⟨5,([false,true,true,false,true,true,false,true]),(rep [false,true,false] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true,true,false,true,true,false] [] [true,true,false] [false,true,false] 3 local3 n (([true])) (([false]))

theorem phase4 (n : Nat) : run0 table 8 ⟨5,([false,true,true,false,true,true,false,true]),(rep [false,true,false] (n)) ++ ([false])⟩ = some ⟨1,[],([true,false,false,true,false,false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,false,true,false,false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false]) = ([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) := by
  calc
    _ = ([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,false,true,false,false,true,false])) ([]) [true,false] false n

theorem growth (n : Nat) : run0 table (23+6*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 1+3*n+14+3*n+8=23+6*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 17 (fun n => 23+6*n) entry (by intro n; omega) growth m hm

#print axioms never

end M217

namespace M240

-- 1RB0RB_1RC0LF_0RD0LE_1LD0RA_0LF---_1LA1LC

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,false,2⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,[],([true,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 4 ⟨0,[],([true,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨3,([true]) ++ (L),([false,false,false,true,false,false]) ++ ([false,true,false,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,false]) ++ (L),([false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨3,([true,false]),([false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [false,false,false,true,false,false] [false,true,false,false] [false,true,true,false] 4 local1 n (([false])) ([])

theorem phase2 (n : Nat) : run0 table 8 ⟨3,([true]) ++ (rep [false,true,true,false] (n)) ++ ([false]),([false,false,false,true,false,false])⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 26 ⟨3,([false,false,true,true,false,false,true,true,false]) ++ ([false,true,true,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (L),([false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (26*n) ⟨3,([false,false,true,true,false,false,true,true,false]) ++ (rep [false,true,true,false] (n)) ++ ([false]),[]⟩ = some ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true,false,false,true,true,false] [] [false,true,true,false] [false,true,false,false] 26 local3 n (([false])) ([])

theorem phase4 (n : Nat) : run0 table 38 ⟨3,([false,false,true,true,false,false,true,true,false,false]),(rep [false,true,false,false] (n))⟩ = some ⟨0,[],([true,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) = ([true,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (50+30*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 4+4*n+8+26*n+38=50+30*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 15 (fun n => 50+30*n) entry (by intro n; omega) growth m hm

#print axioms never

end M240

namespace M251

-- 1RB0RB_1RC0LF_0RD0LA_1LD0RA_0LB---_1LE0LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,true,false,false,true,true,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 159 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 228 ⟨1,([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,true,false,false,true,true,true,false,false,true] (n)),[]⟩ = some ⟨1,([true,false,false,true,true]) ++ (rep [true,true,false,false,true,true,true,false,false,true] (n)),([false,false,false,true,false,false,false,false,true,false,false,false,false,true,false,false,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 58 ⟨1,([true,false,false,true,true]) ++ ([true,true,false,false,true,true,true,false,false,true]) ++ (L),(R)⟩ = some ⟨1,([true,false,false,true,true]) ++ (L),([false,true,false,true,false,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (58*n) ⟨1,([true,false,false,true,true]) ++ (rep [true,true,false,false,true,true,true,false,false,true] (n)),([false,false,false,true,false,false,false,false,true,false,false,false,false,true,false,false,true,false])⟩ = some ⟨1,([true,false,false,true,true]),(rep [false,true,false,true,false,false,true,false,true,false] (n)) ++ ([false,false,false,true,false,false,false,false,true,false,false,false,false,true,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false,true,true] [] [true,true,false,false,true,true,true,false,false,true] [false,true,false,true,false,false,true,false,true,false] 58 local1 n ([]) (([false,false,false,true,false,false,false,false,true,false,false,false,false,true,false,false,true,false]))

theorem phase2 (n : Nat) : run0 table 15 ⟨1,([true,false,false,true,true]),(rep [false,true,false,true,false,false,true,false,true,false] (n)) ++ ([false,false,false,true,false,false,false,false,true,false,false,false,false,true,false,false,true,false])⟩ = some ⟨2,([false,true]),([true,false,false,true,false]) ++ (rep [false,true,false,true,false,false,true,false,true,false] (n)) ++ ([false,false,false,true,false,false,false,false,true,false,false,false,false,true,false,false,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 62 ⟨2,([false]) ++ (L),([true,false,false,true,false]) ++ ([false,true,false,true,false,false,true,false,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,true,false,false,true,true,true,false,false]) ++ (L),([true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (62*n) ⟨2,([false,true]),([true,false,false,true,false]) ++ (rep [false,true,false,true,false,false,true,false,true,false] (n)) ++ ([false,false,false,true,false,false,false,false,true,false,false,false,false,true,false,false,true,false])⟩ = some ⟨2,([false]) ++ (rep [true,true,true,false,false,true,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,false,false,false,false,true,false,false,false,false,true,false,false,false,false,true,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true,false] [false,true,false,true,false,false,true,false,true,false] [true,true,true,false,false,true,true,true,false,false] 62 local3 n (([true])) (([false,false,false,true,false,false,false,false,true,false,false,false,false,true,false,false,true,false]))

theorem phase4 (n : Nat) : run0 table 117 ⟨2,([false]) ++ (rep [true,true,true,false,false,true,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,false,false,false,false,true,false,false,false,false,true,false,false,false,false,true,false,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,true,false,false,true,true,true,false,false]) ++ (rep [true,true,true,false,false,true,true,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,true,false,false,true,true,true,false,false]) ++ (rep [true,true,true,false,false,true,true,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true]) ++ (rep [true,true,false,false,true,true,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true]) ++ (rep [true,true,false,false,true,true,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,true,false,false,true,true,true,false,false])) ([]) [true,true,false,false,true,true,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (360+120*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 228+58*n+15+62*n+117=360+120*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 159 (fun n => 360+120*n) entry (by intro n; omega) growth m hm

#print axioms never

end M251

namespace M252

-- 1RB0RB_1RC0LF_0RD0LA_1LD0RA_0LB---_1LE0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 34 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 8 ⟨2,([false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)),[]⟩ = some ⟨1,([true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)),([false,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 24 ⟨1,([true,false,false,true,true,false,false,true]) ++ ([true,false,false,true,true,false,false,true]) ++ (L),(R)⟩ = some ⟨1,([true,false,false,true,true,false,false,true]) ++ (L),([false,false,true,false,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (24*n) ⟨1,([true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)),([false,true,false])⟩ = some ⟨1,([true,false,false,true,true,false,false,true]),(rep [false,false,true,false,false,false,true,false] (n)) ++ ([false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false,true,true,false,false,true] [] [true,false,false,true,true,false,false,true] [false,false,true,false,false,false,true,false] 24 local1 n ([]) (([false,true,false]))

theorem phase2 (n : Nat) : run0 table 19 ⟨1,([true,false,false,true,true,false,false,true]),(rep [false,false,true,false,false,false,true,false] (n)) ++ ([false,true,false])⟩ = some ⟨2,([false,true]),([true,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([false,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 32 ⟨2,([false]) ++ (L),([true,false,false,true,false,false,false,true,false]) ++ ([false,false,true,false,false,false,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),([true,false,false,true,false,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (32*n) ⟨2,([false,true]),([true,false,false,true,false,false,false,true,false]) ++ (rep [false,false,true,false,false,false,true,false] (n)) ++ ([false,true,false])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,false,false,false,true,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true,false,false,false,true,false] [false,false,true,false,false,false,true,false] [true,true,false,false,true,true,false,false] 32 local3 n (([true])) (([false,true,false]))

theorem phase4 (n : Nat) : run0 table 35 ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,false,false,false,true,false,false,true,false])⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 24 ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),([false,true,false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (24*n) ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([false])⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true]),(rep [false,true,false,false,false,true,false,false] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,false,true,true,false,false,true,true,false,false] [] [true,true,false,false,true,true,false,false] [false,true,false,false,false,true,false,false] 24 local5 n (([true])) (([false]))

theorem phase6 (n : Nat) : run0 table 40 ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true]),(rep [false,true,false,false,false,true,false,false] (n)) ++ ([false])⟩ = some ⟨2,([false,true]),([true,false,false,true,false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false,false,true,false,false] (n)) ++ ([false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 32 ⟨2,([false]) ++ (L),([true,false,false,true,false,false,false,true,false,false,false,true,false,false]) ++ ([false,true,false,false,false,true,false,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),([true,false,false,true,false,false,false,true,false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (32*n) ⟨2,([false,true]),([true,false,false,true,false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false,false,true,false,false] (n)) ++ ([false])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,false,false,false,true,false,false,false,true,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true,false,false,false,true,false,false,false,true,false,false] [false,true,false,false,false,true,false,false] [true,true,false,false,true,true,false,false] 32 local7 n (([true])) (([false]))

theorem phase8 (n : Nat) : run0 table 52 ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,false,false,false,true,false,false,false,true,false,false,false])⟩ = some ⟨2,([false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]) = ([false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false])) ([]) [true,false,false,true,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (154+112*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalL n] at H
  rw [show 8+24*n+19+32*n+35+24*n+40+32*n+52=154+112*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 34 (fun n => 154+112*n) entry (by intro n; omega) growth m hm

#print axioms never

end M252

namespace M253

-- 1RB0RB_1RC0LF_0RD0LA_1LD0RA_0LB---_1LE0LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 34 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 9 ⟨2,([false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)),[]⟩ = some ⟨5,([false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)),([false,false,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 8 ⟨5,([false,false,true,true,false,false,true]) ++ ([true,false,false,true,true,false,false,true]) ++ (L),(R)⟩ = some ⟨5,([false,false,true,true,false,false,true]) ++ (L),([false,false,false,true,false,false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (8*n) ⟨5,([false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)),([false,false,true,false])⟩ = some ⟨5,([false,false,true,true,false,false,true]),(rep [false,false,false,true,false,false,false,true] (n)) ++ ([false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,true,true,false,false,true] [] [true,false,false,true,true,false,false,true] [false,false,false,true,false,false,false,true] 8 local1 n ([]) (([false,false,true,false]))

theorem phase2 (n : Nat) : run0 table 10 ⟨5,([false,false,true,true,false,false,true]),(rep [false,false,false,true,false,false,false,true] (n)) ++ ([false,false,true,false])⟩ = some ⟨2,([false,true]),([true,false,false,true,false,false,false,true]) ++ (rep [false,false,false,true,false,false,false,true] (n)) ++ ([false,false,true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 32 ⟨2,([false]) ++ (L),([true,false,false,true,false,false,false,true]) ++ ([false,false,false,true,false,false,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),([true,false,false,true,false,false,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (32*n) ⟨2,([false,true]),([true,false,false,true,false,false,false,true]) ++ (rep [false,false,false,true,false,false,false,true] (n)) ++ ([false,false,true,false])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,false,false,false,true,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true,false,false,false,true] [false,false,false,true,false,false,false,true] [true,true,false,false,true,true,false,false] 32 local3 n (([true])) (([false,false,true,false]))

theorem phase4 (n : Nat) : run0 table 35 ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,false,false,false,true,false,false,true,false])⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 8 ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),([false,true,false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (8*n) ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([false])⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true]),(rep [false,true,false,false,false,true,false,false] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,false,true,true,false,false,true,true,false,false] [] [true,true,false,false,true,true,false,false] [false,true,false,false,false,true,false,false] 8 local5 n (([true])) (([false]))

theorem phase6 (n : Nat) : run0 table 16 ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true]),(rep [false,true,false,false,false,true,false,false] (n)) ++ ([false])⟩ = some ⟨2,([false,true]),([true,false,false,true,false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false,false,true,false,false] (n)) ++ ([false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 32 ⟨2,([false]) ++ (L),([true,false,false,true,false,false,false,true,false,false,false,true,false,false]) ++ ([false,true,false,false,false,true,false,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),([true,false,false,true,false,false,false,true,false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (32*n) ⟨2,([false,true]),([true,false,false,true,false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false,false,true,false,false] (n)) ++ ([false])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,false,false,false,true,false,false,false,true,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true,false,false,false,true,false,false,false,true,false,false] [false,true,false,false,false,true,false,false] [true,true,false,false,true,true,false,false] 32 local7 n (([true])) (([false]))

theorem phase8 (n : Nat) : run0 table 52 ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,false,false,false,true,false,false,false,true,false,false,false])⟩ = some ⟨2,([false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]) = ([false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false])) ([]) [true,false,false,true,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (122+80*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalL n] at H
  rw [show 9+8*n+10+32*n+35+8*n+16+32*n+52=122+80*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 34 (fun n => 122+80*n) entry (by intro n; omega) growth m hm

#print axioms never

end M253

namespace M254

-- 1RB0RB_1RC0LF_0RD0LA_1LD0RA_0LB---_1LE1RE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨true,true,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 34 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨2,([false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)),[]⟩ = some ⟨4,([false,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)),([true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 12 ⟨4,([false,true,false,false,true,true,false,false,true]) ++ ([true,false,false,true,true,false,false,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,false,false,true,true,false,false,true]) ++ (L),([false,true,false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (12*n) ⟨4,([false,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)),([true,false])⟩ = some ⟨4,([false,true,false,false,true,true,false,false,true]),(rep [false,true,false,false,false,true,false,false] (n)) ++ ([true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,false,false,true,true,false,false,true] [] [true,false,false,true,true,false,false,true] [false,true,false,false,false,true,false,false] 12 local1 n ([]) (([true,false]))

theorem phase2 (n : Nat) : run0 table 14 ⟨4,([false,true,false,false,true,true,false,false,true]),(rep [false,true,false,false,false,true,false,false] (n)) ++ ([true,false])⟩ = some ⟨2,([false,true]),([true,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false,false,true,false,false] (n)) ++ ([true,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 32 ⟨2,([false]) ++ (L),([true,false,false,true,false,false,false,true,false,false]) ++ ([false,true,false,false,false,true,false,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),([true,false,false,true,false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (32*n) ⟨2,([false,true]),([true,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false,false,true,false,false] (n)) ++ ([true,false])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,false,false,false,true,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true,false,false,false,true,false,false] [false,true,false,false,false,true,false,false] [true,true,false,false,true,true,false,false] 32 local3 n (([true])) (([true,false]))

theorem phase4 (n : Nat) : run0 table 35 ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,false,false,false,true,false,false,true,false])⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 12 ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),([false,true,false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (12*n) ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([false])⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true]),(rep [false,true,false,false,false,true,false,false] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,false,true,true,false,false,true,true,false,false] [] [true,true,false,false,true,true,false,false] [false,true,false,false,false,true,false,false] 12 local5 n (([true])) (([false]))

theorem phase6 (n : Nat) : run0 table 22 ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true]),(rep [false,true,false,false,false,true,false,false] (n)) ++ ([false])⟩ = some ⟨2,([false,true]),([true,false,false,true,false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false,false,true,false,false] (n)) ++ ([false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 32 ⟨2,([false]) ++ (L),([true,false,false,true,false,false,false,true,false,false,false,true,false,false]) ++ ([false,true,false,false,false,true,false,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false,true,true,false,false]) ++ (L),([true,false,false,true,false,false,false,true,false,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (32*n) ⟨2,([false,true]),([true,false,false,true,false,false,false,true,false,false,false,true,false,false]) ++ (rep [false,true,false,false,false,true,false,false] (n)) ++ ([false])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,false,false,false,true,false,false,false,true,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true,false,false,false,true,false,false,false,true,false,false] [false,true,false,false,false,true,false,false] [true,true,false,false,true,true,false,false] 32 local7 n (([true])) (([false]))

theorem phase8 (n : Nat) : run0 table 52 ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true,false,false,false,true,false,false,false,true,false,false,false])⟩ = some ⟨2,([false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false] (n)) ++ ([true]) = ([false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false])) ([]) [true,false,false,true,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (130+88*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalL n] at H
  rw [show 7+12*n+14+32*n+35+12*n+22+32*n+52=130+88*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 34 (fun n => 130+88*n) entry (by intro n; omega) growth m hm

#print axioms never

end M254

namespace M255

-- 1RB0RB_1RC0LF_0RD0LB_1LD0RA_0LB---_1LE0RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨1,([true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨1,([true,false,false,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨1,([true,false,false,true]) ++ (L),([false,true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨1,([true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)),[]⟩ = some ⟨1,([true,false,false,true]),(rep [false,true,false,false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false,false,true] [] [false,false,true,false,false,true] [false,true,false,false,true,false] 6 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 7 ⟨1,([true,false,false,true]),(rep [false,true,false,false,true,false] (n))⟩ = some ⟨2,([false,true]),([true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 34 ⟨2,([false]) ++ (L),([true,false,false,true,false]) ++ ([false,true,false,false,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (34*n) ⟨2,([false,true]),([true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n))⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true,false] [false,true,false,false,true,false] [true,false,false,true,false,false] 34 local3 n (([true])) ([])

theorem phase4 (n : Nat) : run0 table 20 ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),([true,false,false,true,false])⟩ = some ⟨1,([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false])) ([]) [false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (33+40*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 6+6*n+7+34*n+20=33+40*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 33+40*n) entry (by intro n; omega) growth m hm

#print axioms never

end M255

namespace M256

-- 1RB0RB_1RC0LF_0RD0LC_1LD0RA_0LB---_1LE1RD

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨true,true,3⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,false,true,false,false,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨1,([false,true]) ++ (rep [false,false,true,false,false,false,true] (n)),[]⟩ = some ⟨3,([false,false,true,true]) ++ (rep [false,false,true,false,false,false,true] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 23 ⟨3,([false,false,true,true]) ++ ([false,false,true,false,false,false,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true]) ++ (L),([true,false,false,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (23*n) ⟨3,([false,false,true,true]) ++ (rep [false,false,true,false,false,false,true] (n)),[]⟩ = some ⟨3,([false,false,true,true]),(rep [true,false,false,false,false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true] [] [false,false,true,false,false,false,true] [true,false,false,false,false,true,false] 23 local1 n ([]) ([])

theorem phase2 (n : Nat) : run0 table 28 ⟨3,([false,false,true,true]),(rep [true,false,false,false,false,true,false] (n))⟩ = some ⟨2,([false,true]),([true,false,true,false,false,false]) ++ (rep [true,false,false,false,false,true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 53 ⟨2,([false]) ++ (L),([true,false,true,false,false,false]) ++ ([true,false,false,false,false,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false,false]) ++ (L),([true,false,true,false,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (53*n) ⟨2,([false,true]),([true,false,true,false,false,false]) ++ (rep [true,false,false,false,false,true,false] (n))⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false,false] (n)) ++ ([true]),([true,false,true,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,true,false,false,false] [true,false,false,false,false,true,false] [true,false,false,true,false,false,false] 53 local3 n (([true])) ([])

theorem phase4 (n : Nat) : run0 table 21 ⟨2,([false]) ++ (rep [true,false,false,true,false,false,false] (n)) ++ ([true]),([true,false,true,false,false,false])⟩ = some ⟨1,([false,true,false,false,true,false,false,false]) ++ (rep [true,false,false,true,false,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,false,false,false]) ++ (rep [true,false,false,true,false,false,false] (n)) ++ ([true]) = ([false,true,false,false,true,false,false,false,true]) ++ (rep [false,false,true,false,false,false,true] (n)) := by
  calc
    _ = ([false,true,false,false,true,false,false,false,true]) ++ (rep [false,false,true,false,false,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,false,false,false])) ([]) [false,false,true,false,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (51+76*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 2+23*n+28+53*n+21=51+76*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 51+76*n) entry (by intro n; omega) growth m hm

#print axioms never

end M256

end BB6.Agent11Raw39B0RBPumps
