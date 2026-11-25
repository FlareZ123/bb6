import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39Pumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M1925

-- 1RB1RB_1RC1LF_0RD0RA_1LD0RA_0LB---_1LE0LE

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
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],(rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n)) ++ ([true,false,false,true])⟩

theorem entry : run0 table 11 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 3 ⟨5,[],(rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n)) ++ ([true,false,false,true])⟩ = some ⟨2,([false,true]),([true]) ++ (rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n)) ++ ([true,false,false,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 20 ⟨2,([false]) ++ (L),([true]) ++ ([true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (20*n) ⟨2,([false,true]),([true]) ++ (rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n)) ++ ([true,false,false,true])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true] [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] 20 local1 n (([true])) (([true,false,false,true]))

theorem phase2 (n : Nat) : run0 table 18 ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,true,false,false,true])⟩ = some ⟨4,([false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,true,false,false,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 60 ⟨4,([false,true,true,false,false]) ++ ([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),(R)⟩ = some ⟨4,([false,true,true,false,false]) ++ (L),([false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (60*n) ⟨4,([false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,true,false,false,true])⟩ = some ⟨4,([false,true,true,false,false,true]),(rep [false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false] (n)) ++ ([true,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true,false,false] [] [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] [false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false] 60 local3 n (([true])) (([true,true,false,false,true]))

theorem phase4 (n : Nat) : run0 table 17 ⟨4,([false,true,true,false,false,true]),(rep [false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false] (n)) ++ ([true,true,false,false,true])⟩ = some ⟨2,([false,true]),([true,true,false,false,true,true,false]) ++ (rep [false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false] (n)) ++ ([true,true,false,false,true])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 20 ⟨2,([false]) ++ (L),([true,true,false,false,true,true,false]) ++ ([false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),([true,true,false,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (20*n) ⟨2,([false,true]),([true,true,false,false,true,true,false]) ++ (rep [false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false] (n)) ++ ([true,true,false,false,true])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,true,false,false,true,true,false,true,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,false,true,true,false] [false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false] [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] 20 local5 n (([true])) (([true,true,false,false,true]))

theorem phase6 (n : Nat) : run0 table 26 ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,true,false,false,true,true,false,true,true,false,false,true])⟩ = some ⟨1,([true,true,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([false,true,true,false,false,true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 60 ⟨1,([true,true,false,true,true,false,false,true,true,false,false]) ++ ([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,true,true,false,false,true,true,false,false]) ++ (L),([true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (60*n) ⟨1,([true,true,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([false,true,true,false,false,true])⟩ = some ⟨1,([true,true,false,true,true,false,false,true,true,false,false,true]),(rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n)) ++ ([false,true,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,true,true,false,false,true,true,false,false] [] [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] 60 local7 n (([true])) (([false,true,true,false,false,true]))

theorem phase8 (n : Nat) : run0 table 31 ⟨1,([true,true,false,true,true,false,false,true,true,false,false,true]),(rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n)) ++ ([false,true,true,false,false,true])⟩ = some ⟨2,([false,true]),([true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n)) ++ ([false,true,true,false,false,true])⟩ := by rfl

theorem local9 (L R : List Bool) : run0 table 20 ⟨2,([false]) ++ (L),([true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ ([true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),([true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase9 (n : Nat) : run0 table (20*n) ⟨2,([false,true]),([true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n)) ++ ([false,true,true,false,false,true])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,true,false,false,true,true,false,false,true,true,false,false,true,false,true,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,false,true,true,false,false,true,true,false,false,true] [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] 20 local9 n (([true])) (([false,true,true,false,false,true]))

theorem phase10 (n : Nat) : run0 table 15 ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,true,false,false,true,true,false,false,true,true,false,false,true,false,true,true,false,false,true])⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true])⟩ := by rfl

theorem local11 (L R : List Bool) : run0 table 60 ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ ([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),([false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true]) ++ (R)⟩ := by rfl

theorem phase11 (n : Nat) : run0 table (60*n) ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,false,false,true])⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]),(rep [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] (n)) ++ ([true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] [] [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] 60 local11 n (([true])) (([true,false,false,true]))

theorem phase12 (n : Nat) : run0 table 52 ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]),(rep [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] (n)) ++ ([true,false,false,true])⟩ = some ⟨2,([false,true]),([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true]) ++ (rep [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] (n)) ++ ([true,false,false,true])⟩ := by rfl

theorem local13 (L R : List Bool) : run0 table 20 ⟨2,([false]) ++ (L),([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true]) ++ ([false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true]) ++ (R)⟩ := by rfl

theorem phase13 (n : Nat) : run0 table (20*n) ⟨2,([false,true]),([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true]) ++ (rep [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] (n)) ++ ([true,false,false,true])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] 20 local13 n (([true])) (([true,false,false,true]))

theorem phase14 (n : Nat) : run0 table 19 ⟨2,([false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,true,false,false,true])⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([false,false,true])⟩ := by rfl

theorem local15 (L R : List Bool) : run0 table 60 ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ ([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (L),([false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true]) ++ (R)⟩ := by rfl

theorem phase15 (n : Nat) : run0 table (60*n) ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false]) ++ (rep [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] (n)) ++ ([true]),([false,false,true])⟩ = some ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]),(rep [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] (n)) ++ ([false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] [] [true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false] [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] 60 local15 n (([true])) (([false,false,true]))

theorem phase16 (n : Nat) : run0 table 61 ⟨1,([true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]),(rep [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] (n)) ++ ([false,false,true])⟩ = some ⟨5,[],([true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true]) ++ (rep [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] (n)) ++ ([false,false,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true]) ++ (rep [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true] (n)) ++ ([false,false,true]) = ([true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n)) ++ ([true,false,false,true]) := by
  calc
    _ = ([true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true]) ++ (rep [true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] (n)) ++ ([true,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true])) (([false,false,true])) [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true] true n

theorem growth (n : Nat) : run0 table (242+320*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n)) (phase9 n)) (phase10 n)) (phase11 n)) (phase12 n)) (phase13 n)) (phase14 n)) (phase15 n)) (phase16 n))
  rw [finalR n] at H
  rw [show 3+20*n+18+60*n+17+20*n+26+60*n+31+20*n+15+60*n+52+20*n+19+60*n+61=242+320*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 11 (fun n => 242+320*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1925

namespace M1930

-- 1RB1RB_1RC1LF_0RD0RC_1LD0RA_0LB---_1RD0LE

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
  | 5,false => some (some ⟨true,true,3⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,(rep [false] (n)) ++ ([false,false,false,true,true,false]) ++ (rep [true] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 17 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 1 ⟨3,([false]) ++ (L),(R)⟩ = some ⟨3,(L),([true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (1*n) ⟨3,(rep [false] (n)) ++ ([false,false,false,true,true,false]) ++ (rep [true] (n)) ++ ([true]),[]⟩ = some ⟨3,([false,false,false,true,true,false]) ++ (rep [true] (n)) ++ ([true]),(rep [true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [] [] [false] [true] 1 local0 n (([false,false,false,true,true,false]) ++ (rep [true] (n)) ++ ([true])) ([])

theorem phase1 (n : Nat) : run0 table 13 ⟨3,([false,false,false,true,true,false]) ++ (rep [true] (n)) ++ ([true]),(rep [true] (n))⟩ = some ⟨2,([true,true,true,false,true]) ++ (rep [true] (n)) ++ ([true]),([true]) ++ (rep [true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 1 ⟨2,([true]) ++ (L),([true]) ++ ([true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (1*n) ⟨2,([true,true,true,false,true]) ++ (rep [true] (n)) ++ ([true]),([true]) ++ (rep [true] (n))⟩ = some ⟨2,([true]) ++ (rep [false] (n)) ++ ([true,true,false,true]) ++ (rep [true] (n)) ++ ([true]),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true] [true] [false] 1 local2 n (([true,true,false,true]) ++ (rep [true] (n)) ++ ([true])) ([])

theorem phase3 (n : Nat) : run0 table 3 ⟨2,([true]) ++ (rep [false] (n)) ++ ([true,true,false,true]) ++ (rep [true] (n)) ++ ([true]),([true])⟩ = some ⟨3,([false,false,false,false]) ++ (rep [false] (n)) ++ ([true,true,false,true]) ++ (rep [true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,false]) ++ (rep [false] (n)) ++ ([true,true,false,true]) ++ (rep [true] (n)) ++ ([true]) = ([false]) ++ (rep [false] (n)) ++ ([false,false,false,true,true,false,true]) ++ (rep [true] (n)) ++ ([true]) := by
  calc
    _ = ([false,false,false]) ++ (rep [false] (n)) ++ ([false,true,true,false,true]) ++ (rep [true] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false])) (([true,true,false,true]) ++ (rep [true] (n)) ++ ([true])) [] false n
    _ = ([false,false]) ++ (rep [false] (n)) ++ ([false,false,true,true,false,true]) ++ (rep [true] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,true,true,false,true]) ++ (rep [true] (n)) ++ ([true])) [] false n
    _ = ([false]) ++ (rep [false] (n)) ++ ([false,false,false,true,true,false,true]) ++ (rep [true] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,true,true,false,true]) ++ (rep [true] (n)) ++ ([true])) [] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (16+2*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 1*n+13+1*n+3=16+2*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 17 (fun n => 16+2*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1930

namespace M1961

-- 1RB1RB_1RC1LF_0RD0RC_1LD0RA_1LE0LB_---0LE

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
  | 4,false => some (some ⟨true,false,4⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,(rep [false] (n)) ++ ([false,false,false,true,true,false,false]) ++ (rep [true] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 27 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 1 ⟨3,([false]) ++ (L),(R)⟩ = some ⟨3,(L),([true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (1*n) ⟨3,(rep [false] (n)) ++ ([false,false,false,true,true,false,false]) ++ (rep [true] (n)) ++ ([true]),[]⟩ = some ⟨3,([false,false,false,true,true,false,false]) ++ (rep [true] (n)) ++ ([true]),(rep [true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [] [] [false] [true] 1 local0 n (([false,false,false,true,true,false,false]) ++ (rep [true] (n)) ++ ([true])) ([])

theorem phase1 (n : Nat) : run0 table 23 ⟨3,([false,false,false,true,true,false,false]) ++ (rep [true] (n)) ++ ([true]),(rep [true] (n))⟩ = some ⟨2,([true,true,true,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true]) ++ (rep [true] (n))⟩ := by rfl

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

theorem growth (n : Nat) : run0 table (26+2*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 1*n+23+1*n+3=26+2*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 27 (fun n => 26+2*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1961

namespace M1999

-- 1RB1RB_1RC1LF_0RD0RE_1LD0RA_0RB---_0LD0LF

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
  | 5,false => some (some ⟨false,false,3⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ = some ⟨3,([false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 7 ⟨3,([false,false,true]) ++ ([false,false,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true]) ++ (L),([false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (7*n) ⟨3,([false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true]) ++ (rep [false] (n)),[]⟩ = some ⟨3,([false,false,true,true]) ++ (rep [false] (n)),(rep [false,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true] [] [false,false,true] [false,false,true] 7 local1 n (([true]) ++ (rep [false] (n))) ([])

theorem phase2 (n : Nat) : run0 table 9 ⟨3,([false,false,true,true]) ++ (rep [false] (n)),(rep [false,false,true] (n))⟩ = some ⟨1,([false,true,false]) ++ (rep [false] (n)),([true]) ++ (rep [false,false,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([false]) ++ (L),([true]) ++ ([false,false,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,false,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([false,true,false]) ++ (rep [false] (n)),([true]) ++ (rep [false,false,true] (n))⟩ = some ⟨1,([false]) ++ (rep [false,false,true] (n)) ++ ([true,false]) ++ (rep [false] (n)),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true] [false,false,true] [false,false,true] 3 local3 n (([true,false]) ++ (rep [false] (n))) ([])

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

end M1999

namespace M2046

-- 1RB1RB_1RC1LF_0RD1LC_1LD0RA_0LB---_1LE0RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true,false]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true]),[]⟩

theorem entry : run0 table 44 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 11 ⟨1,([false,true,false]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true]),[]⟩ = some ⟨1,([true,false]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true]),([false,true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 10 ⟨1,([true,false]) ++ ([false,true,true,false,true,true]) ++ (L),(R)⟩ = some ⟨1,([true,false]) ++ (L),([false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (10*n) ⟨1,([true,false]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true]),([false,true,true])⟩ = some ⟨1,([true,false,false,true,true,false,true]),(rep [false,true,true,false,true,true] (n)) ++ ([false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,false] [] [false,true,true,false,true,true] [false,true,true,false,true,true] 10 local1 n (([false,true,true,false,true])) (([false,true,true]))

theorem phase2 (n : Nat) : run0 table 12 ⟨1,([true,false,false,true,true,false,true]),(rep [false,true,true,false,true,true] (n)) ++ ([false,true,true])⟩ = some ⟨2,([false,true]),([true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 50 ⟨2,([false]) ++ (L),([true,true,false,true,true,false,true,true]) ++ ([false,true,true,false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,false,true,true,false]) ++ (L),([true,true,false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (50*n) ⟨2,([false,true]),([true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true])⟩ = some ⟨2,([false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,true,false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true,true,false,true,true] [false,true,true,false,true,true] [true,true,false,true,true,false] 50 local3 n (([true])) (([false,true,true]))

theorem phase4 (n : Nat) : run0 table 78 ⟨2,([false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),([true,true,false,true,true,false,true,true,false,true,true])⟩ = some ⟨1,([false,true,false,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]) = ([false,true,false,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true]) := by
  calc
    _ = ([false,true,false,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,true,true,false,true,true])) (([true])) [true,true,false,true,true] false n
    _ = ([false,true,false,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,true,true,false,true])) (([false,true])) [false,true,true,false,true] true n
    _ = ([false,true,false,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true,true,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,true,true,false])) (([true,false,true])) [true,false,true,true,false] true n
    _ = ([false,true,false,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,true,true,false,true,true])) (([true,true,false,true])) [true,true,false,true,true] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (101+60*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 11+10*n+12+50*n+78=101+60*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 44 (fun n => 101+60*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2046

namespace M2117

-- 1RB1RB_1RC1LF_0RD1LC_1LD0RA_0LB---_1LE1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true,false]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true]),[]⟩

theorem entry : run0 table 38 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 11 ⟨1,([false,true,false]) ++ (rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true]),[]⟩ = some ⟨4,(rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true]),([true,true,false,true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨4,([false,true,true,false,true,true]) ++ (L),(R)⟩ = some ⟨4,(L),([true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨4,(rep [false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true]),([true,true,false,true,true])⟩ = some ⟨4,([false,true,true,false,true]),(rep [true,true,false,true,true,false] (n)) ++ ([true,true,false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [] [] [false,true,true,false,true,true] [true,true,false,true,true,false] 6 local1 n (([false,true,true,false,true])) (([true,true,false,true,true]))

theorem phase2 (n : Nat) : run0 table 8 ⟨4,([false,true,true,false,true]),(rep [true,true,false,true,true,false] (n)) ++ ([true,true,false,true,true])⟩ = some ⟨2,([false,true]),([true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true,true,false,true,true])⟩ := by rfl

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

end M2117

namespace M2118

-- 1RB1RB_1RC1LF_0RD1LC_1LD0RA_0LB---_1RB1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,true,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
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

end M2118

namespace M2136

-- 1RB1RB_1RC1LF_0RD0RC_1LD0RA_1LB---_0LB1LE

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
  | 4,false => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
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

end M2136

namespace M2137

-- 1RB1RB_1RC1LF_0RD0RC_1LD0RA_1LB---_0LE1LE

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
  | 4,false => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨true,false,4⟩)
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

end M2137

namespace M2244

-- 1RB1RB_1RC1LF_0RD0RC_1LD0RA_---0LB_1LE1RF

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
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨true,true,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,(rep [false] (n)) ++ ([false,false,false,true,true,false]) ++ (rep [false,true] (n)) ++ ([false,true]),[]⟩

theorem entry : run0 table 22 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 1 ⟨3,([false]) ++ (L),(R)⟩ = some ⟨3,(L),([true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (1*n) ⟨3,(rep [false] (n)) ++ ([false,false,false,true,true,false]) ++ (rep [false,true] (n)) ++ ([false,true]),[]⟩ = some ⟨3,([false,false,false,true,true,false]) ++ (rep [false,true] (n)) ++ ([false,true]),(rep [true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [] [] [false] [true] 1 local0 n (([false,false,false,true,true,false]) ++ (rep [false,true] (n)) ++ ([false,true])) ([])

theorem phase1 (n : Nat) : run0 table 6 ⟨3,([false,false,false,true,true,false]) ++ (rep [false,true] (n)) ++ ([false,true]),(rep [true] (n))⟩ = some ⟨5,([true,false,true,false]) ++ (rep [false,true] (n)) ++ ([false,true]),([true,true]) ++ (rep [true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 1 ⟨5,([true]) ++ (L),([true,true]) ++ ([true]) ++ (R)⟩ = some ⟨5,([true]) ++ ([true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (1*n) ⟨5,([true,false,true,false]) ++ (rep [false,true] (n)) ++ ([false,true]),([true,true]) ++ (rep [true] (n))⟩ = some ⟨5,([true]) ++ (rep [true] (n)) ++ ([false,true,false]) ++ (rep [false,true] (n)) ++ ([false,true]),([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 5 [true] [true,true] [true] [true] 1 local2 n (([false,true,false]) ++ (rep [false,true] (n)) ++ ([false,true])) ([])

theorem phase3 (n : Nat) : run0 table 3 ⟨5,([true]) ++ (rep [true] (n)) ++ ([false,true,false]) ++ (rep [false,true] (n)) ++ ([false,true]),([true,true])⟩ = some ⟨5,([false,true,true,true]) ++ (rep [true] (n)) ++ ([false,true,false]) ++ (rep [false,true] (n)) ++ ([false,true]),[]⟩ := by rfl

theorem local4 (L R : List Bool) : run0 table 5 ⟨5,([false,true,true,true]) ++ ([true]) ++ (L),(R)⟩ = some ⟨5,([false,true,true,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase4 (n : Nat) : run0 table (5*n) ⟨5,([false,true,true,true]) ++ (rep [true] (n)) ++ ([false,true,false]) ++ (rep [false,true] (n)) ++ ([false,true]),[]⟩ = some ⟨5,([false,true,true,true,false,true,false]) ++ (rep [false,true] (n)) ++ ([false,true]),(rep [true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true,true,true] [] [true] [true] 5 local4 n (([false,true,false]) ++ (rep [false,true] (n)) ++ ([false,true])) ([])

theorem phase5 (n : Nat) : run0 table 15 ⟨5,([false,true,true,true,false,true,false]) ++ (rep [false,true] (n)) ++ ([false,true]),(rep [true] (n))⟩ = some ⟨2,([true,true,true,false,false,true]) ++ (rep [false,true] (n)) ++ ([false,true]),([true]) ++ (rep [true] (n))⟩ := by rfl

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

end M2244

end BB6.Agent11Raw39Pumps
