import SweepPumping

set_option maxRecDepth 100000

set_option maxHeartbeats 0

set_option linter.unusedVariables false

namespace BB6.Agent11Raw121Pumps

open BB6Coverage BB6Coverage.Agent31Pump

namespace M41

-- 1RB0LF_1RC0LA_0RD---_1LD1RE_0LA1RE_0RA1LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([false,false]) ++ (rep [false,true,false] (n)) ++ ([false,true,false,false])⟩

theorem entry : run0 table 16 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨5,[],([false,false]) ++ (rep [false,true,false] (n)) ++ ([false,true,false,false])⟩ = some ⟨0,[false,false],([false]) ++ (rep [false,true,false] (n)) ++ ([false,true,false,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 7 ⟨0,([false]) ++ (L),([false]) ++ ([false,true,false]) ++ (R)⟩ = some ⟨0,([false]) ++ ([false,true,true]) ++ (L),([false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (7*n) ⟨0,[false,false],([false]) ++ (rep [false,true,false] (n)) ++ ([false,true,false,false])⟩ = some ⟨0,([false]) ++ (rep [false,true,true] (n)) ++ ([false]),[false,false,true,false,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [false] [false] [false,true,false] [false,true,true] 7 local1 n [false] [false,true,false,false]

theorem phase2 (n : Nat) : run0 table 15 ⟨0,([false]) ++ (rep [false,true,true] (n)) ++ ([false]),[false,false,true,false,false]⟩ = some ⟨4,([false,true,true,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 23 ⟨4,([false,true,true,true,true,false,true,true]) ++ ([false,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true,true,true,false,true,true]) ++ (L),([true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (23*n) ⟨4,([false,true,true,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false]),[]⟩ = some ⟨4,[false,true,true,true,true,false,true,true,false],(rep [true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true,true,true,false,true,true] [] [false,true,true] [true,false,false] 23 local3 n [false] []

theorem phase4 (n : Nat) : run0 table 31 ⟨4,[false,true,true,true,true,false,true,true,false],(rep [true,false,false] (n))⟩ = some ⟨5,[],([false,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) = ([false,false,false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false,true,false,false]) := by
  calc
    _ = ([false,false,false,true,false,false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,false,false,true,false,false,true,false] [] [true,false] false n
    _ = ([false,false,false,true,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,false,false,true,false,false,true] [false] [false,true] false n
    _ = ([false,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,false,false,true,false,false] [false,false] [false,false] true n
    _ = ([false,false,false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,false,false,true,false] [true,false,false] [true,false] false n

theorem growth (n : Nat) : run0 table (47+30*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 1+7*n+15+23*n+31=47+30*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 16 (fun n => 47+30*n) entry (by intro n; omega) growth m hm

#print axioms never

end M41

namespace M43

-- 1RB0LF_1RC0LD_0RD---_1LD1RE_0LA1RE_0RA1LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([false,false]) ++ (rep [false,true,false] (n)) ++ ([false,true,false,false])⟩

theorem entry : run0 table 18 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨5,[],([false,false]) ++ (rep [false,true,false] (n)) ++ ([false,true,false,false])⟩ = some ⟨0,[false,false],([false]) ++ (rep [false,true,false] (n)) ++ ([false,true,false,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 7 ⟨0,([false]) ++ (L),([false]) ++ ([false,true,false]) ++ (R)⟩ = some ⟨0,([false]) ++ ([false,true,true]) ++ (L),([false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (7*n) ⟨0,[false,false],([false]) ++ (rep [false,true,false] (n)) ++ ([false,true,false,false])⟩ = some ⟨0,([false]) ++ (rep [false,true,true] (n)) ++ ([false]),[false,false,true,false,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [false] [false] [false,true,false] [false,true,true] 7 local1 n [false] [false,true,false,false]

theorem phase2 (n : Nat) : run0 table 15 ⟨0,([false]) ++ (rep [false,true,true] (n)) ++ ([false]),[false,false,true,false,false]⟩ = some ⟨4,([false,true,true,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 27 ⟨4,([false,true,true,true,true,false,true,true]) ++ ([false,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true,true,true,false,true,true]) ++ (L),([true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (27*n) ⟨4,([false,true,true,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false]),[]⟩ = some ⟨4,[false,true,true,true,true,false,true,true,false],(rep [true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true,true,true,false,true,true] [] [false,true,true] [true,false,false] 27 local3 n [false] []

theorem phase4 (n : Nat) : run0 table 37 ⟨4,[false,true,true,true,true,false,true,true,false],(rep [true,false,false] (n))⟩ = some ⟨5,[],([false,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) = ([false,false,false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false,true,false,false]) := by
  calc
    _ = ([false,false,false,true,false,false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,false,false,true,false,false,true,false] [] [true,false] false n
    _ = ([false,false,false,true,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,false,false,true,false,false,true] [false] [false,true] false n
    _ = ([false,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,false,false,true,false,false] [false,false] [false,false] true n
    _ = ([false,false,false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,false,false,true,false] [true,false,false] [true,false] false n

theorem growth (n : Nat) : run0 table (53+34*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 1+7*n+15+27*n+37=53+34*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 18 (fun n => 53+34*n) entry (by intro n; omega) growth m hm

#print axioms never

end M43

namespace M44

-- 1RB0LF_1RC0LE_0RD---_1LD1RE_0LA1RE_0RA1LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([false,false]) ++ (rep [false,true,false] (n)) ++ ([false,true,false,false])⟩

theorem entry : run0 table 18 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨5,[],([false,false]) ++ (rep [false,true,false] (n)) ++ ([false,true,false,false])⟩ = some ⟨0,[false,false],([false]) ++ (rep [false,true,false] (n)) ++ ([false,true,false,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 7 ⟨0,([false]) ++ (L),([false]) ++ ([false,true,false]) ++ (R)⟩ = some ⟨0,([false]) ++ ([false,true,true]) ++ (L),([false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (7*n) ⟨0,[false,false],([false]) ++ (rep [false,true,false] (n)) ++ ([false,true,false,false])⟩ = some ⟨0,([false]) ++ (rep [false,true,true] (n)) ++ ([false]),[false,false,true,false,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [false] [false] [false,true,false] [false,true,true] 7 local1 n [false] [false,true,false,false]

theorem phase2 (n : Nat) : run0 table 15 ⟨0,([false]) ++ (rep [false,true,true] (n)) ++ ([false]),[false,false,true,false,false]⟩ = some ⟨4,([false,true,true,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 27 ⟨4,([false,true,true,true,true,false,true,true]) ++ ([false,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true,true,true,false,true,true]) ++ (L),([true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (27*n) ⟨4,([false,true,true,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false]),[]⟩ = some ⟨4,[false,true,true,true,true,false,true,true,false],(rep [true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true,true,true,false,true,true] [] [false,true,true] [true,false,false] 27 local3 n [false] []

theorem phase4 (n : Nat) : run0 table 37 ⟨4,[false,true,true,true,true,false,true,true,false],(rep [true,false,false] (n))⟩ = some ⟨5,[],([false,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) = ([false,false,false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false,true,false,false]) := by
  calc
    _ = ([false,false,false,true,false,false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,false,false,true,false,false,true,false] [] [true,false] false n
    _ = ([false,false,false,true,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,false,false,true,false,false,true] [false] [false,true] false n
    _ = ([false,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,false,false,true,false,false] [false,false] [false,false] true n
    _ = ([false,false,false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,false,false,true,false] [true,false,false] [true,false] false n

theorem growth (n : Nat) : run0 table (53+34*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 1+7*n+15+27*n+37=53+34*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 18 (fun n => 53+34*n) entry (by intro n; omega) growth m hm

#print axioms never

end M44

namespace M45

-- 1RB0LF_1RC0RE_0RD1RA_1LD1RE_0LA1RE_---1LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true]) ++ (rep [true,true,true,true] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨2,([false,true]) ++ (rep [true,true,true,true] (n)) ++ ([true]),[]⟩ = some ⟨0,([true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true]),[false]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨0,([true,true,true]) ++ ([true,true,true,true]) ++ (L),(R)⟩ = some ⟨0,([true,true,true]) ++ (L),([true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨0,([true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true]),[false]⟩ = some ⟨0,[true,true,true,true],(rep [true,false,true,false] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,true,true] [] [true,true,true,true] [true,false,true,false] 4 local1 n [true] [false]

theorem phase2 (n : Nat) : run0 table 5 ⟨0,[true,true,true,true],(rep [true,false,true,false] (n)) ++ ([false])⟩ = some ⟨1,[true,true],([false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨1,([true]) ++ (L),([false,true,false]) ++ ([true,false,true,false]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,true,true,true]) ++ (L),([false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨1,[true,true],([false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([false])⟩ = some ⟨1,([true]) ++ (rep [true,true,true,true] (n)) ++ ([true]),[false,true,false,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,true,false] [true,false,true,false] [true,true,true,true] 6 local3 n [true] [false]

theorem phase4 (n : Nat) : run0 table 7 ⟨1,([true]) ++ (rep [true,true,true,true] (n)) ++ ([true]),[false,true,false,false]⟩ = some ⟨2,([false,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true]) = ([false,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (19+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 7+4*n+5+6*n+7=19+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 19+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M45

namespace M942

-- 1RB1LF_1RC0LB_0RD---_1LD1RE_0LA1RE_---1LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,[],([true]) ++ (rep [true,true] (n)) ++ ([true,true,true,false])⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 8 ⟨0,[],([true]) ++ (rep [true,true] (n)) ++ ([true,true,true,false])⟩ = some ⟨4,[true,true],([true]) ++ (rep [true,true] (n)) ++ ([true,true,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨4,([true]) ++ (L),([true]) ++ ([true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨4,[true,true],([true]) ++ (rep [true,true] (n)) ++ ([true,true,true,false])⟩ = some ⟨4,([true]) ++ (rep [true,true] (n)) ++ ([true]),[true,true,true,true,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true] [true,true] [true,true] 2 local1 n [true] [true,true,true,false]

theorem phase2 (n : Nat) : run0 table 6 ⟨4,([true]) ++ (rep [true,true] (n)) ++ ([true]),[true,true,true,true,false]⟩ = some ⟨0,([true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true]),[false]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 2 ⟨0,([true,true,true,true,true]) ++ ([true,true]) ++ (L),(R)⟩ = some ⟨0,([true,true,true,true,true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (2*n) ⟨0,([true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true]),[false]⟩ = some ⟨0,[true,true,true,true,true,true],(rep [true,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,true,true,true,true] [] [true,true] [true,true] 2 local3 n [true] [false]

theorem phase4 (n : Nat) : run0 table 6 ⟨0,[true,true,true,true,true,true],(rep [true,true] (n)) ++ ([false])⟩ = some ⟨0,[],([true,true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false]) = ([true,true,true]) ++ (rep [true,true] (n)) ++ ([true,true,true,false]) := by
  calc
    _ = ([true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,true,true,true,true] [false] [true] true n
    _ = ([true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,true,true,true] [true,false] [true] true n
    _ = ([true,true,true]) ++ (rep [true,true] (n)) ++ ([true,true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,true,true] [true,true,false] [true] true n

theorem growth (n : Nat) : run0 table (20+4*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 8+2*n+6+2*n+6=20+4*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 20+4*n) entry (by intro n; omega) growth m hm

#print axioms never

end M942

namespace M943

-- 1RB1LF_1RC0LC_0RD0LB_1LD1RE_0LA1RE_---1LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,[],([true]) ++ (rep [true,true] (n)) ++ ([true,true,true,false])⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 8 ⟨0,[],([true]) ++ (rep [true,true] (n)) ++ ([true,true,true,false])⟩ = some ⟨4,[true,true],([true]) ++ (rep [true,true] (n)) ++ ([true,true,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨4,([true]) ++ (L),([true]) ++ ([true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨4,[true,true],([true]) ++ (rep [true,true] (n)) ++ ([true,true,true,false])⟩ = some ⟨4,([true]) ++ (rep [true,true] (n)) ++ ([true]),[true,true,true,true,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true] [true,true] [true,true] 2 local1 n [true] [true,true,true,false]

theorem phase2 (n : Nat) : run0 table 6 ⟨4,([true]) ++ (rep [true,true] (n)) ++ ([true]),[true,true,true,true,false]⟩ = some ⟨0,([true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true]),[false]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 2 ⟨0,([true,true,true,true,true]) ++ ([true,true]) ++ (L),(R)⟩ = some ⟨0,([true,true,true,true,true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (2*n) ⟨0,([true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true]),[false]⟩ = some ⟨0,[true,true,true,true,true,true],(rep [true,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,true,true,true,true] [] [true,true] [true,true] 2 local3 n [true] [false]

theorem phase4 (n : Nat) : run0 table 6 ⟨0,[true,true,true,true,true,true],(rep [true,true] (n)) ++ ([false])⟩ = some ⟨0,[],([true,true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false]) = ([true,true,true]) ++ (rep [true,true] (n)) ++ ([true,true,true,false]) := by
  calc
    _ = ([true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,true,true,true,true] [false] [true] true n
    _ = ([true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,true,true,true] [true,false] [true] true n
    _ = ([true,true,true]) ++ (rep [true,true] (n)) ++ ([true,true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,true,true] [true,true,false] [true] true n

theorem growth (n : Nat) : run0 table (20+4*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 8+2*n+6+2*n+6=20+4*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 20+4*n) entry (by intro n; omega) growth m hm

#print axioms never

end M943

namespace M1358

-- 1RB1LF_1RC1LA_0RD---_1LD1RE_0LB1RE_0LE1LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],(rep [true,true,true] (n)) ++ ([true,true,true,true,true,false])⟩

theorem entry : run0 table 16 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨5,[],(rep [true,true,true] (n)) ++ ([true,true,true,true,true,false])⟩ = some ⟨4,[true,true],([true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨4,([true]) ++ (L),([true]) ++ ([true,true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨4,[true,true],([true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,true,false])⟩ = some ⟨4,([true]) ++ (rep [true,true,true] (n)) ++ ([true]),[true,true,true,true,true,true,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true] [true,true,true] [true,true,true] 3 local1 n [true] [true,true,true,true,true,false]

theorem phase2 (n : Nat) : run0 table 8 ⟨4,([true]) ++ (rep [true,true,true] (n)) ++ ([true]),[true,true,true,true,true,true,false]⟩ = some ⟨1,([true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]),[false]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([true,true,true,true,true,true,true]) ++ ([true,true,true]) ++ (L),(R)⟩ = some ⟨1,([true,true,true,true,true,true,true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]),[false]⟩ = some ⟨1,[true,true,true,true,true,true,true,true],(rep [true,true,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,true,true,true,true,true] [] [true,true,true] [true,true,true] 3 local3 n [true] [false]

theorem phase4 (n : Nat) : run0 table 8 ⟨1,[true,true,true,true,true,true,true,true],(rep [true,true,true] (n)) ++ ([false])⟩ = some ⟨5,[],([true,true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false]) = ([true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,true,false]) := by
  calc
    _ = ([true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,true,true,true,true,true,true] [false] [true,true] true n
    _ = ([true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,true,true,true,true,true] [true,false] [true,true] true n
    _ = ([true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,true,true,true,true] [true,true,false] [true,true] true n
    _ = ([true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,true,true,true] [true,true,true,false] [true,true] true n
    _ = ([true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,true,true] [true,true,true,true,false] [true,true] true n

theorem growth (n : Nat) : run0 table (23+6*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 7+3*n+8+3*n+8=23+6*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 16 (fun n => 23+6*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1358

namespace M1840

-- 1RB1LB_1RC1LF_0RD---_1LD1RE_0LB1RE_0LE1LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],(rep [true,true,true] (n)) ++ ([true,true,true,true,false])⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨5,[],(rep [true,true,true] (n)) ++ ([true,true,true,true,false])⟩ = some ⟨4,[true,true],([true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨4,([true]) ++ (L),([true]) ++ ([true,true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨4,[true,true],([true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,false])⟩ = some ⟨4,([true]) ++ (rep [true,true,true] (n)) ++ ([true]),[true,true,true,true,true,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true] [true,true,true] [true,true,true] 3 local1 n [true] [true,true,true,true,false]

theorem phase2 (n : Nat) : run0 table 7 ⟨4,([true]) ++ (rep [true,true,true] (n)) ++ ([true]),[true,true,true,true,true,false]⟩ = some ⟨1,([true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]),[false]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([true,true,true,true,true,true]) ++ ([true,true,true]) ++ (L),(R)⟩ = some ⟨1,([true,true,true,true,true,true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,([true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]),[false]⟩ = some ⟨1,[true,true,true,true,true,true,true],(rep [true,true,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,true,true,true,true] [] [true,true,true] [true,true,true] 3 local3 n [true] [false]

theorem phase4 (n : Nat) : run0 table 7 ⟨1,[true,true,true,true,true,true,true],(rep [true,true,true] (n)) ++ ([false])⟩ = some ⟨5,[],([true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false]) = ([true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,false]) := by
  calc
    _ = ([true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,true,true,true,true,true] [false] [true,true] true n
    _ = ([true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,true,true,true,true] [true,false] [true,true] true n
    _ = ([true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,true,true,true] [true,true,false] [true,true] true n
    _ = ([true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,true,true] [true,true,true,false] [true,true] true n

theorem growth (n : Nat) : run0 table (21+6*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 7+3*n+7+3*n+7=21+6*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 21+6*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1840

namespace M2082

-- 1RB0LF_1RC---_0RD0LA_1LD1RE_0LC1RE_0LA1LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,2⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([false]) ++ (rep [true,false] (n)) ++ ([true,false,false,false])⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨5,[],([false]) ++ (rep [true,false] (n)) ++ ([true,false,false,false])⟩ = some ⟨1,[false,true],([false]) ++ (rep [true,false] (n)) ++ ([true,false,false,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨1,([false]) ++ (L),([false]) ++ ([true,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,true]) ++ (L),([false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨1,[false,true],([false]) ++ (rep [true,false] (n)) ++ ([true,false,false,false])⟩ = some ⟨1,([false]) ++ (rep [true,true] (n)) ++ ([true]),[false,true,false,false,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [false] [true,false] [true,true] 6 local1 n [true] [true,false,false,false]

theorem phase2 (n : Nat) : run0 table 15 ⟨1,([false]) ++ (rep [true,true] (n)) ++ ([true]),[false,true,false,false,false]⟩ = some ⟨0,([true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true]),[false,false]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 2 ⟨0,([true,true,true,true]) ++ ([true,true]) ++ (L),(R)⟩ = some ⟨0,([true,true,true,true]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (2*n) ⟨0,([true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true]),[false,false]⟩ = some ⟨0,[true,true,true,true,true],(rep [true,false] (n)) ++ ([false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,true,true,true] [] [true,true] [true,false] 2 local3 n [true] [false,false]

theorem phase4 (n : Nat) : run0 table 5 ⟨0,[true,true,true,true,true],(rep [true,false] (n)) ++ ([false,false])⟩ = some ⟨5,[],([false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([false,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([false,false]) = ([false,true,false]) ++ (rep [true,false] (n)) ++ ([true,false,false,false]) := by
  calc
    _ = ([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([false,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,false,true] [false,false] [true] false n
    _ = ([false,true,false]) ++ (rep [true,false] (n)) ++ ([true,false,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,false] [false,false,false] [false] true n

theorem growth (n : Nat) : run0 table (22+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 2+6*n+15+2*n+5=22+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 22+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2082

namespace M2083

-- 1RB0LF_1RC---_0RD0LA_1LD1RE_0LC1RE_1LC1LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,2⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],(rep [false,true] (n)) ++ ([false,true,false,false,false])⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨5,[],(rep [false,true] (n)) ++ ([false,true,false,false,false])⟩ = some ⟨3,[true,false],(rep [false,true] (n)) ++ ([false,true,false,false,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨3,([true,false]) ++ (L),([false,true]) ++ (R)⟩ = some ⟨3,([true,false]) ++ ([true,true]) ++ (L),(R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨3,[true,false],(rep [false,true] (n)) ++ ([false,true,false,false,false])⟩ = some ⟨3,([true,false]) ++ (rep [true,true] (n)),[false,true,false,false,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true,false] [] [false,true] [true,true] 6 local1 n [] [false,true,false,false,false]

theorem phase2 (n : Nat) : run0 table 19 ⟨3,([true,false]) ++ (rep [true,true] (n)),[false,true,false,false,false]⟩ = some ⟨0,([true,true,true,true,true]) ++ (rep [true,true] (n)),[false,false]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 2 ⟨0,([true,true,true,true,true]) ++ ([true,true]) ++ (L),(R)⟩ = some ⟨0,([true,true,true,true,true]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (2*n) ⟨0,([true,true,true,true,true]) ++ (rep [true,true] (n)),[false,false]⟩ = some ⟨0,[true,true,true,true,true],(rep [true,false] (n)) ++ ([false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,true,true,true,true] [] [true,true] [true,false] 2 local3 n [] [false,false]

theorem phase4 (n : Nat) : run0 table 5 ⟨0,[true,true,true,true,true],(rep [true,false] (n)) ++ ([false,false])⟩ = some ⟨5,[],([false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([false,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([false,false]) = ([false,true]) ++ (rep [false,true] (n)) ++ ([false,true,false,false,false]) := by
  calc
    _ = ([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([false,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,false,true] [false,false] [true] false n
    _ = ([false,true,false]) ++ (rep [true,false] (n)) ++ ([true,false,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,false] [false,false,false] [false] true n
    _ = ([false,true]) ++ (rep [false,true] (n)) ++ ([false,true,false,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true] [true,false,false,false] [true] false n

theorem growth (n : Nat) : run0 table (26+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 2+6*n+19+2*n+5=26+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 26+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2083

namespace M2084

-- 1RB0LF_1RC---_0RD0LA_1LD1RE_0LC1RE_1RE1LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,2⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([false]) ++ (rep [true,false] (n)) ++ ([true,false,false,false])⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 4 ⟨5,[],([false]) ++ (rep [true,false] (n)) ++ ([true,false,false,false])⟩ = some ⟨1,[false,true],([false]) ++ (rep [true,false] (n)) ++ ([true,false,false,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨1,([false]) ++ (L),([false]) ++ ([true,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,true]) ++ (L),([false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨1,[false,true],([false]) ++ (rep [true,false] (n)) ++ ([true,false,false,false])⟩ = some ⟨1,([false]) ++ (rep [true,true] (n)) ++ ([true]),[false,true,false,false,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [false] [true,false] [true,true] 6 local1 n [true] [true,false,false,false]

theorem phase2 (n : Nat) : run0 table 15 ⟨1,([false]) ++ (rep [true,true] (n)) ++ ([true]),[false,true,false,false,false]⟩ = some ⟨0,([true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true]),[false,false]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 2 ⟨0,([true,true,true,true]) ++ ([true,true]) ++ (L),(R)⟩ = some ⟨0,([true,true,true,true]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (2*n) ⟨0,([true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true]),[false,false]⟩ = some ⟨0,[true,true,true,true,true],(rep [true,false] (n)) ++ ([false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,true,true,true] [] [true,true] [true,false] 2 local3 n [true] [false,false]

theorem phase4 (n : Nat) : run0 table 5 ⟨0,[true,true,true,true,true],(rep [true,false] (n)) ++ ([false,false])⟩ = some ⟨5,[],([false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([false,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([false,false]) = ([false,true,false]) ++ (rep [true,false] (n)) ++ ([true,false,false,false]) := by
  calc
    _ = ([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([false,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,false,true] [false,false] [true] false n
    _ = ([false,true,false]) ++ (rep [true,false] (n)) ++ ([true,false,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,false] [false,false,false] [false] true n

theorem growth (n : Nat) : run0 table (24+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 4+6*n+15+2*n+5=24+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 24+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2084

namespace M2241

-- 1RB1LF_1RC0LB_0RD1LF_1LD1RE_0LC1RE_---1LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,2⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,[],([true]) ++ (rep [true,true] (n)) ++ ([true,true,true,false])⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 8 ⟨0,[],([true]) ++ (rep [true,true] (n)) ++ ([true,true,true,false])⟩ = some ⟨4,[true,true],([true]) ++ (rep [true,true] (n)) ++ ([true,true,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨4,([true]) ++ (L),([true]) ++ ([true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨4,[true,true],([true]) ++ (rep [true,true] (n)) ++ ([true,true,true,false])⟩ = some ⟨4,([true]) ++ (rep [true,true] (n)) ++ ([true]),[true,true,true,true,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true] [true,true] [true,true] 2 local1 n [true] [true,true,true,false]

theorem phase2 (n : Nat) : run0 table 7 ⟨4,([true]) ++ (rep [true,true] (n)) ++ ([true]),[true,true,true,true,false]⟩ = some ⟨5,([true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true]),[true,false]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 2 ⟨5,([true,true,true,true]) ++ ([true,true]) ++ (L),(R)⟩ = some ⟨5,([true,true,true,true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (2*n) ⟨5,([true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true]),[true,false]⟩ = some ⟨5,[true,true,true,true,true],(rep [true,true] (n)) ++ ([true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,true,true,true] [] [true,true] [true,true] 2 local3 n [true] [true,false]

theorem phase4 (n : Nat) : run0 table 5 ⟨5,[true,true,true,true,true],(rep [true,true] (n)) ++ ([true,false])⟩ = some ⟨0,[],([true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,false]) = ([true,true,true]) ++ (rep [true,true] (n)) ++ ([true,true,true,false]) := by
  calc
    _ = ([true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,true,true,true] [true,false] [true] true n
    _ = ([true,true,true]) ++ (rep [true,true] (n)) ++ ([true,true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,true,true] [true,true,false] [true] true n

theorem growth (n : Nat) : run0 table (20+4*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 8+2*n+7+2*n+5=20+4*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 20+4*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2241

namespace M2437

-- 1RB1LE_1RC0RF_0RD---_1LD1RE_0LF1RE_1RA0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false,true,true,true,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true]),[]⟩

theorem entry : run0 table 34 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 15 ⟨4,([false,true,true,true,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true]),[]⟩ = some ⟨4,([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true]),[false,false,false]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨4,([false,true,true]) ++ ([false,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true]) ++ (L),([true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨4,([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true]),[false,false,false]⟩ = some ⟨4,[false,true,true,false,true,true],(rep [true,false,false] (n)) ++ ([false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true] [] [false,true,true] [true,false,false] 3 local1 n [false,true,true] [false,false,false]

theorem phase2 (n : Nat) : run0 table 8 ⟨4,[false,true,true,false,true,true],(rep [true,false,false] (n)) ++ ([false,false,false])⟩ = some ⟨0,[false,true],([true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false,false,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨0,([false]) ++ (L),([true,false,false,true,false,false]) ++ ([true,false,false]) ++ (R)⟩ = some ⟨0,([false]) ++ ([true,false,true]) ++ (L),([true,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨0,[false,true],([true,false,false,true,false,false]) ++ (rep [true,false,false] (n)) ++ ([false,false,false])⟩ = some ⟨0,([false]) ++ (rep [true,false,true] (n)) ++ ([true]),[true,false,false,true,false,false,false,false,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [false] [true,false,false,true,false,false] [true,false,false] [true,false,true] 3 local3 n [true] [false,false,false]

theorem phase4 (n : Nat) : run0 table 14 ⟨0,([false]) ++ (rep [true,false,true] (n)) ++ ([true]),[true,false,false,true,false,false,false,false,false]⟩ = some ⟨4,([false,true,true,true,true,true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true]) = ([false,true,true,true,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true]) := by
  calc
    _ = ([false,true,true,true,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,false,true,true,false] [true] [true,false] true n
    _ = ([false,true,true,true,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,false,true,true] [true,true] [true,true] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (37+6*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 15+3*n+8+3*n+14=37+6*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 34 (fun n => 37+6*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2437

namespace M2460

-- 1RB1LF_1RC0LD_0RD---_1LD1RE_0LF1RE_1LA0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true,true]),[]⟩

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨4,([false]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true,true]),[]⟩ = some ⟨5,(rep [true,true,true,true] (n)) ++ ([true,true,true,true]),[false]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨5,([true,true,true,true]) ++ (L),(R)⟩ = some ⟨5,(L),([true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨5,(rep [true,true,true,true] (n)) ++ ([true,true,true,true]),[false]⟩ = some ⟨5,[true,true,true,true],(rep [true,false,true,false] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [] [] [true,true,true,true] [true,false,true,false] 4 local1 n [true,true,true,true] [false]

theorem phase2 (n : Nat) : run0 table 11 ⟨5,[true,true,true,true],(rep [true,false,true,false] (n)) ++ ([false])⟩ = some ⟨1,[false,true],([false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 12 ⟨1,([false]) ++ (L),([false,true,false,true,false]) ++ ([true,false,true,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,true,true,true]) ++ (L),([false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (12*n) ⟨1,[false,true],([false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([false])⟩ = some ⟨1,([false]) ++ (rep [true,true,true,true] (n)) ++ ([true]),[false,true,false,true,false,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [false,true,false,true,false] [true,false,true,false] [true,true,true,true] 12 local3 n [true] [false]

theorem phase4 (n : Nat) : run0 table 19 ⟨1,([false]) ++ (rep [true,true,true,true] (n)) ++ ([true]),[false,true,false,true,false,false]⟩ = some ⟨4,([false,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true]) = ([false,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true,true]) := by
  calc
    _ = ([false,true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true] [true] [true,true,true] true n
    _ = ([false,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true] [true,true] [true,true,true] true n
    _ = ([false,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true] [true,true,true] [true,true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (31+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 1+4*n+11+12*n+19=31+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (fun n => 31+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2460

namespace M2461

-- 1RB1LF_1RC0LE_0RD---_1LD1RE_0LF1RE_1LA0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true,true]),[]⟩

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨4,([false]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true,true]),[]⟩ = some ⟨5,(rep [true,true,true,true] (n)) ++ ([true,true,true,true]),[false]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨5,([true,true,true,true]) ++ (L),(R)⟩ = some ⟨5,(L),([true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨5,(rep [true,true,true,true] (n)) ++ ([true,true,true,true]),[false]⟩ = some ⟨5,[true,true,true,true],(rep [true,false,true,false] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [] [] [true,true,true,true] [true,false,true,false] 4 local1 n [true,true,true,true] [false]

theorem phase2 (n : Nat) : run0 table 11 ⟨5,[true,true,true,true],(rep [true,false,true,false] (n)) ++ ([false])⟩ = some ⟨1,[false,true],([false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 12 ⟨1,([false]) ++ (L),([false,true,false,true,false]) ++ ([true,false,true,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,true,true,true]) ++ (L),([false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (12*n) ⟨1,[false,true],([false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([false])⟩ = some ⟨1,([false]) ++ (rep [true,true,true,true] (n)) ++ ([true]),[false,true,false,true,false,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [false,true,false,true,false] [true,false,true,false] [true,true,true,true] 12 local3 n [true] [false]

theorem phase4 (n : Nat) : run0 table 19 ⟨1,([false]) ++ (rep [true,true,true,true] (n)) ++ ([true]),[false,true,false,true,false,false]⟩ = some ⟨4,([false,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true]) = ([false,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true,true]) := by
  calc
    _ = ([false,true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true] [true] [true,true,true] true n
    _ = ([false,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true] [true,true] [true,true,true] true n
    _ = ([false,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true] [true,true,true] [true,true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (31+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 1+4*n+11+12*n+19=31+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (fun n => 31+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2461

namespace M2462

-- 1RB1LF_1RC0LF_0RD---_1LD1RE_0LF1RE_1LA0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true,true]),[]⟩

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨4,([false]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true,true]),[]⟩ = some ⟨5,(rep [true,true,true,true] (n)) ++ ([true,true,true,true]),[false]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨5,([true,true,true,true]) ++ (L),(R)⟩ = some ⟨5,(L),([true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨5,(rep [true,true,true,true] (n)) ++ ([true,true,true,true]),[false]⟩ = some ⟨5,[true,true,true,true],(rep [true,false,true,false] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [] [] [true,true,true,true] [true,false,true,false] 4 local1 n [true,true,true,true] [false]

theorem phase2 (n : Nat) : run0 table 9 ⟨5,[true,true,true,true],(rep [true,false,true,false] (n)) ++ ([false])⟩ = some ⟨1,[false,true],([false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 12 ⟨1,([false]) ++ (L),([false,true,false,true,false]) ++ ([true,false,true,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,true,true,true]) ++ (L),([false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (12*n) ⟨1,[false,true],([false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([false])⟩ = some ⟨1,([false]) ++ (rep [true,true,true,true] (n)) ++ ([true]),[false,true,false,true,false,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [false,true,false,true,false] [true,false,true,false] [true,true,true,true] 12 local3 n [true] [false]

theorem phase4 (n : Nat) : run0 table 19 ⟨1,([false]) ++ (rep [true,true,true,true] (n)) ++ ([true]),[false,true,false,true,false,false]⟩ = some ⟨4,([false,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true]) = ([false,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true,true]) := by
  calc
    _ = ([false,true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true] [true] [true,true,true] true n
    _ = ([false,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true] [true,true] [true,true,true] true n
    _ = ([false,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true] [true,true,true] [true,true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (29+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 1+4*n+9+12*n+19=29+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (fun n => 29+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2462

namespace M2799

-- 1RB1LB_1RC0RC_0RD0LE_1LD1RE_0LF1RE_---1LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([true]) ++ (rep [true,false] (n)) ++ ([true,false,false,true,false])⟩

theorem entry : run0 table 34 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨1,[],([true]) ++ (rep [true,false] (n)) ++ ([true,false,false,true,false])⟩ = some ⟨1,[true,true],([false]) ++ (rep [true,false] (n)) ++ ([true,false,false,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨1,([true]) ++ (L),([false]) ++ ([true,false]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false]) ++ (L),([false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨1,[true,true],([false]) ++ (rep [true,false] (n)) ++ ([true,false,false,true,false])⟩ = some ⟨1,([true]) ++ (rep [true,false] (n)) ++ ([true]),[false,true,false,false,true,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false] [true,false] [true,false] 6 local1 n [true] [true,false,false,true,false]

theorem phase2 (n : Nat) : run0 table 21 ⟨1,([true]) ++ (rep [true,false] (n)) ++ ([true]),[false,true,false,false,true,false]⟩ = some ⟨4,([false,true,true,false]) ++ (rep [true,false] (n)) ++ ([true]),[false,true,false]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨4,([false,true,true,false]) ++ ([true,false]) ++ (L),(R)⟩ = some ⟨4,([false,true,true,false]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨4,([false,true,true,false]) ++ (rep [true,false] (n)) ++ ([true]),[false,true,false]⟩ = some ⟨4,[false,true,true,false,true],(rep [true,false] (n)) ++ ([false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true,false] [] [true,false] [true,false] 6 local3 n [true] [false,true,false]

theorem phase4 (n : Nat) : run0 table 9 ⟨4,[false,true,true,false,true],(rep [true,false] (n)) ++ ([false,true,false])⟩ = some ⟨1,[],([true,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([false,true,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([false,true,false]) = ([true,true,false]) ++ (rep [true,false] (n)) ++ ([true,false,false,true,false]) := by
  calc
    _ = ([true,true,false,true]) ++ (rep [false,true] (n)) ++ ([false,false,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,true,false,true] [false,true,false] [true] false n
    _ = ([true,true,false]) ++ (rep [true,false] (n)) ++ ([true,false,false,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,true,false] [false,false,true,false] [false] true n

theorem growth (n : Nat) : run0 table (36+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 6+6*n+21+6*n+9=36+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 34 (fun n => 36+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2799

namespace M2939

-- 1RB1LF_1RC0LA_0RD1RC_1LD1RE_0LF1RE_---1LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨3,([false,false,true]) ++ (rep [true,true,true] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 3 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨3,([false,false,true]) ++ (rep [true,true,true] (n)) ++ ([true]),[]⟩ = some ⟨5,([true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]),[false]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨5,([true,true,true]) ++ ([true,true,true]) ++ (L),(R)⟩ = some ⟨5,([true,true,true]) ++ (L),([true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨5,([true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]),[false]⟩ = some ⟨5,[true,true,true,true],(rep [true,false,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,true,true] [] [true,true,true] [true,false,true] 3 local1 n [true] [false]

theorem phase2 (n : Nat) : run0 table 6 ⟨5,[true,true,true,true],(rep [true,false,true] (n)) ++ ([false])⟩ = some ⟨2,[true,true,true],([false,true]) ++ (rep [true,false,true] (n)) ++ ([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 9 ⟨2,([true]) ++ (L),([false,true]) ++ ([true,false,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true,true]) ++ (L),([false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (9*n) ⟨2,[true,true,true],([false,true]) ++ (rep [true,false,true] (n)) ++ ([false])⟩ = some ⟨2,([true]) ++ (rep [true,true,true] (n)) ++ ([true,true]),[false,true,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,true] [true,false,true] [true,true,true] 9 local3 n [true,true] [false]

theorem phase4 (n : Nat) : run0 table 8 ⟨2,([true]) ++ (rep [true,true,true] (n)) ++ ([true,true]),[false,true,false]⟩ = some ⟨3,([false,false,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true]) = ([false,false,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]) := by
  calc
    _ = ([false,false,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,false,true,true,true] [true] [true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (20+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 6+3*n+6+9*n+8=20+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 3 (fun n => 20+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2939

namespace M3114

-- 1RB---_1RC1LF_0RD1RA_1LD1RE_0LF1RE_0LB1LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,false])⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 4 ⟨5,[],([true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,false])⟩ = some ⟨4,[true,true,false,true],(rep [true,true,true,true] (n)) ++ ([true,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨4,([true]) ++ (L),([true,true,true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true,true,true]) ++ (L),(R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨4,[true,true,false,true],(rep [true,true,true,true] (n)) ++ ([true,true,false])⟩ = some ⟨4,([true]) ++ (rep [true,true,true,true] (n)) ++ ([true,false,true]),[true,true,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [] [true,true,true,true] [true,true,true,true] 4 local1 n [true,false,true] [true,true,false]

theorem phase2 (n : Nat) : run0 table 4 ⟨4,([true]) ++ (rep [true,true,true,true] (n)) ++ ([true,false,true]),[true,true,false]⟩ = some ⟨5,([true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,false,true]),[false]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 4 ⟨5,([true,true,true]) ++ ([true,true,true,true]) ++ (L),(R)⟩ = some ⟨5,([true,true,true]) ++ (L),([true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (4*n) ⟨5,([true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,false,true]),[false]⟩ = some ⟨5,[true,true,true,true,false,true],(rep [true,true,true,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,true,true] [] [true,true,true,true] [true,true,true,true] 4 local3 n [true,false,true] [false]

theorem phase4 (n : Nat) : run0 table 20 ⟨5,[true,true,true,true,false,true],(rep [true,true,true,true] (n)) ++ ([false])⟩ = some ⟨5,[],([true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([false]) = ([true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,false]) := by
  calc
    _ = ([true,true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,true,true,true,true,true,true] [false] [true,true,true] true n
    _ = ([true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,true,true,true,true,true] [true,false] [true,true,true] true n

theorem growth (n : Nat) : run0 table (28+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 4+4*n+4+4*n+20=28+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 28+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M3114

namespace M4128

-- 1RB0LA_1RC1LB_0RD1LA_1LD1RE_0RF1RE_1LA---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true]),[]⟩

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 3 ⟨4,([false]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true]),[]⟩ = some ⟨1,([true,true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true]),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 8 ⟨1,([true,true]) ++ ([true,true,true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨1,([true,true]) ++ (L),([true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (8*n) ⟨1,([true,true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true]),[]⟩ = some ⟨1,[true,true,true,true,true,true],(rep [true,true,true,true,true,true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true] [] [true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] 8 local1 n [true,true,true,true] []

theorem phase2 (n : Nat) : run0 table 18 ⟨1,[true,true,true,true,true,true],(rep [true,true,true,true,true,true,true,true] (n))⟩ = some ⟨4,[true,true,false,true,true],([true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 8 ⟨4,([true]) ++ (L),([true,true,true,true]) ++ ([true,true,true,true,true,true,true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true,true,true,true,true,true,true]) ++ (L),([true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (8*n) ⟨4,[true,true,false,true,true],([true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true] (n))⟩ = some ⟨4,([true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true,false,true,true]),[true,true,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true,true,true,true] [true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] 8 local3 n [true,false,true,true] []

theorem phase4 (n : Nat) : run0 table 8 ⟨4,([true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true,false,true,true]),[true,true,true,true]⟩ = some ⟨1,([true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true,false,true,true]),[]⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 8 ⟨1,([true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨1,([true,true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (8*n) ⟨1,([true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true,false,true,true]),[]⟩ = some ⟨1,[true,true,true,true,true,true,true,true,false,true,true],(rep [true,true,true,true,true,true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] 8 local5 n [true,false,true,true] []

theorem phase6 (n : Nat) : run0 table 19 ⟨1,[true,true,true,true,true,true,true,true,false,true,true],(rep [true,true,true,true,true,true,true,true] (n))⟩ = some ⟨4,[true,true,true],([true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true] (n))⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 8 ⟨4,([true]) ++ (L),([true,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true,true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (8*n) ⟨4,[true,true,true],([true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true] (n))⟩ = some ⟨4,([true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true,true]),[true,true,true,true,true,true,true,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] 8 local7 n [true,true] []

theorem phase8 (n : Nat) : run0 table 10 ⟨4,([true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true,true]),[true,true,true,true,true,true,true,true,true]⟩ = some ⟨4,([false,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true,true]) = ([false,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true]) := by
  calc
    _ = ([false,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true,true,true,true] [true,true] [true,true,true,true,true,true,true] true n
    _ = ([false,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true,true,true] [true,true,true] [true,true,true,true,true,true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (58+32*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalL n] at H
  rw [show 3+8*n+18+8*n+8+8*n+19+8*n+10=58+32*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (fun n => 58+32*n) entry (by intro n; omega) growth m hm

#print axioms never

end M4128

namespace M4745

-- 1RB0LF_1RC1RF_0RD---_1LD1RE_1LA1RE_0RA0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 11 ⟨1,([false]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]),[]⟩ = some ⟨4,([false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]),[false,true]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨4,([false,true]) ++ ([true,false,true,true,false,true]) ++ (L),(R)⟩ = some ⟨4,([false,true]) ++ (L),([false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨4,([false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]),[false,true]⟩ = some ⟨4,[false,true,true],(rep [false,false,true,false,false,true] (n)) ++ ([false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true] [] [true,false,true,true,false,true] [false,false,true,false,false,true] 6 local1 n [true] [false,true]

theorem phase2 (n : Nat) : run0 table 5 ⟨4,[false,true,true],(rep [false,false,true,false,false,true] (n)) ++ ([false,true])⟩ = some ⟨1,[true,true],([false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([false,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨1,([true]) ++ (L),([false,false,true]) ++ ([false,false,true,false,false,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true,true,false,true]) ++ (L),([false,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨1,[true,true],([false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([false,true])⟩ = some ⟨1,([true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]),[false,false,true,false,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,false,true] [false,false,true,false,false,true] [true,false,true,true,false,true] 6 local3 n [true] [false,true]

theorem phase4 (n : Nat) : run0 table 8 ⟨1,([true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]),[false,false,true,false,true]⟩ = some ⟨1,([false,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]) = ([false,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (24+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 11+6*n+5+6*n+8=24+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 24+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M4745

namespace M4942

-- 1RB0LF_1RC0RA_0RD---_1LD1RE_1LA1RE_1LA1RC

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,true,2⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 27 ⟨1,([false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)),[]⟩ = some ⟨0,([true,false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)),[true,true,true]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 10 ⟨0,([true,false,true]) ++ ([false,true,false,true,false,true,false,true,false,true]) ++ (L),(R)⟩ = some ⟨0,([true,false,true]) ++ (L),([true,false,true,false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (10*n) ⟨0,([true,false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)),[true,true,true]⟩ = some ⟨0,[true,false,true],(rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,false,true] [] [false,true,false,true,false,true,false,true,false,true] [true,false,true,false,true,false,true,false,true,false] 10 local1 n [] [true,true,true]

theorem phase2 (n : Nat) : run0 table 5 ⟨0,[true,false,true],(rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true,true,true])⟩ = some ⟨1,[true,true],([false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true,true,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 10 ⟨1,([true]) ++ (L),([false,true,false]) ++ ([true,false,true,false,true,false,true,false,true,false]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true,false,true,false,true,false,true,false]) ++ (L),([false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (10*n) ⟨1,[true,true],([false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true,true,true])⟩ = some ⟨1,([true]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),[false,true,false,true,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,true,false] [true,false,true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false,true,false] 10 local3 n [true] [true,true,true]

theorem phase4 (n : Nat) : run0 table 5 ⟨1,([true]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),[false,true,false,true,true,true]⟩ = some ⟨0,([true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),[true]⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 10 ⟨0,([true,false,true,false,true,false]) ++ ([true,false,true,false,true,false,true,false,true,false]) ++ (L),(R)⟩ = some ⟨0,([true,false,true,false,true,false]) ++ (L),([true,false,true,false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (10*n) ⟨0,([true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),[true]⟩ = some ⟨0,[true,false,true,false,true,false,true],(rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,false,true,false,true,false] [] [true,false,true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false,true,false] 10 local5 n [true] [true]

theorem phase6 (n : Nat) : run0 table 9 ⟨0,[true,false,true,false,true,false,true],(rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])⟩ = some ⟨1,[true,true],([false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 10 ⟨1,([true]) ++ (L),([false,true,false,true,false,true,false]) ++ ([true,false,true,false,true,false,true,false,true,false]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true,false,true,false,true,false,true,false]) ++ (L),([false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (10*n) ⟨1,[true,true],([false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])⟩ = some ⟨1,([true]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),[false,true,false,true,false,true,false,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false,true,false] 10 local7 n [true] [true]

theorem phase8 (n : Nat) : run0 table 10 ⟨1,([true]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),[false,true,false,true,false,true,false,true]⟩ = some ⟨1,([false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]) = ([false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)) := by
  calc
    _ = ([false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,false,true,false,true,false,true,false,true,false] [] [false,true,false,true,false,true,false,true,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (56+40*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalL n] at H
  rw [show 27+10*n+5+10*n+5+10*n+9+10*n+10=56+40*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 56+40*n) entry (by intro n; omega) growth m hm

#print axioms never

end M4942

namespace M5270

-- 1RB1LA_1RC0RF_0RD0RA_1LD1RE_1LA1RE_---0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true]),[]⟩

theorem entry : run0 table 25 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨2,([false,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true]),[]⟩ = some ⟨0,([true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true]),[true]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 9 ⟨0,([true,true,true]) ++ ([true,true,true,true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨0,([true,true,true]) ++ (L),([true,true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (9*n) ⟨0,([true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true]),[true]⟩ = some ⟨0,[true,true,true,true,true,true,true,true],(rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,true,true] [] [true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true] 9 local1 n [true,true,true,true,true] [true]

theorem phase2 (n : Nat) : run0 table 9 ⟨0,[true,true,true,true,true,true,true,true],(rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨1,[true,true],([true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 21 ⟨1,([true]) ++ (L),([true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,true,true,true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (21*n) ⟨1,[true,true],([true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨1,([true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),[true,true,true,true,true,true,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true] 21 local3 n [true] [true]

theorem phase4 (n : Nat) : run0 table 44 ⟨1,([true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),[true,true,true,true,true,true,true,true]⟩ = some ⟨2,([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true]) = ([false,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true]) := by
  calc
    _ = ([false,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true,true,true,true,true,true,true,true] [true] [true,true,true,true,true,true,true,true] true n
    _ = ([false,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true,true,true,true,true,true,true] [true,true] [true,true,true,true,true,true,true,true] true n
    _ = ([false,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true,true,true,true,true,true] [true,true,true] [true,true,true,true,true,true,true,true] true n
    _ = ([false,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true,true,true,true,true] [true,true,true,true] [true,true,true,true,true,true,true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (60+30*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 7+9*n+9+21*n+44=60+30*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 25 (fun n => 60+30*n) entry (by intro n; omega) growth m hm

#print axioms never

end M5270

namespace M5277

-- 1RB1LA_1RC0RF_0RD1RB_1LD1RE_1LA1RE_---0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 8 ⟨1,([false]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ = some ⟨0,([true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),[true]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 9 ⟨0,([true,true,true]) ++ ([true,true,true,true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨0,([true,true,true]) ++ (L),([true,true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (9*n) ⟨0,([true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),[true]⟩ = some ⟨0,[true,true,true,true],(rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,true,true] [] [true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true] 9 local1 n [true] [true]

theorem phase2 (n : Nat) : run0 table 5 ⟨0,[true,true,true,true],(rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨1,[true,true],([true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 15 ⟨1,([true]) ++ (L),([true,true,true]) ++ ([true,true,true,true,true,true,true,true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,true,true,true,true,true,true,true,true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (15*n) ⟨1,[true,true],([true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨1,([true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),[true,true,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,true,true] [true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true] 15 local3 n [true] [true]

theorem phase4 (n : Nat) : run0 table 16 ⟨1,([true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),[true,true,true,true]⟩ = some ⟨0,([true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),[true]⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 9 ⟨0,([true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨0,([true,true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (9*n) ⟨0,([true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),[true]⟩ = some ⟨0,[true,true,true,true,true,true,true,true],(rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true] 9 local5 n [true] [true]

theorem phase6 (n : Nat) : run0 table 9 ⟨0,[true,true,true,true,true,true,true,true],(rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨1,[true,true],([true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 15 ⟨1,([true]) ++ (L),([true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,true,true,true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (15*n) ⟨1,[true,true],([true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨1,([true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),[true,true,true,true,true,true,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true] 15 local7 n [true] [true]

theorem phase8 (n : Nat) : run0 table 15 ⟨1,([true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),[true,true,true,true,true,true,true,true]⟩ = some ⟨1,([false,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true]) = ([false,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (53+48*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 8+9*n+5+15*n+16+9*n+9+15*n+15=53+48*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 53+48*n) entry (by intro n; omega) growth m hm

#print axioms never

end M5277

namespace M5517

-- 1RB1LA_1RC1RF_0RD1RB_1LD1RE_1LA1RE_---0LC

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨false,false,2⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 8 ⟨1,([false]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ = some ⟨0,([true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),[true]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 9 ⟨0,([true,true,true]) ++ ([true,true,true,true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨0,([true,true,true]) ++ (L),([true,true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (9*n) ⟨0,([true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),[true]⟩ = some ⟨0,[true,true,true,true],(rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,true,true] [] [true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true] 9 local1 n [true] [true]

theorem phase2 (n : Nat) : run0 table 5 ⟨0,[true,true,true,true],(rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨1,[true,true],([true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 15 ⟨1,([true]) ++ (L),([true,true,true]) ++ ([true,true,true,true,true,true,true,true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,true,true,true,true,true,true,true,true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (15*n) ⟨1,[true,true],([true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨1,([true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),[true,true,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,true,true] [true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true] 15 local3 n [true] [true]

theorem phase4 (n : Nat) : run0 table 16 ⟨1,([true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),[true,true,true,true]⟩ = some ⟨0,([true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),[true]⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 9 ⟨0,([true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨0,([true,true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (9*n) ⟨0,([true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),[true]⟩ = some ⟨0,[true,true,true,true,true,true,true,true],(rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true] 9 local5 n [true] [true]

theorem phase6 (n : Nat) : run0 table 9 ⟨0,[true,true,true,true,true,true,true,true],(rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨1,[true,true],([true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 15 ⟨1,([true]) ++ (L),([true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,true,true,true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (15*n) ⟨1,[true,true],([true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨1,([true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),[true,true,true,true,true,true,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true] 15 local7 n [true] [true]

theorem phase8 (n : Nat) : run0 table 15 ⟨1,([true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),[true,true,true,true,true,true,true,true]⟩ = some ⟨1,([false,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true]) = ([false,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true] (n)) ++ ([true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (53+48*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 8+9*n+5+15*n+16+9*n+9+15*n+15=53+48*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 53+48*n) entry (by intro n; omega) growth m hm

#print axioms never

end M5517

namespace M5837

-- 1RB1LC_1RC---_0RD0LF_1LD1RE_1LA1RE_1LC1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,[],([true,false]) ++ (rep [true,true] (n)) ++ ([true,true,true,true])⟩

theorem entry : run0 table 18 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨2,[],([true,false]) ++ (rep [true,true] (n)) ++ ([true,true,true,true])⟩ = some ⟨4,[true,true,false],(rep [true,true] (n)) ++ ([true,true,true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨4,([true]) ++ (L),([true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true]) ++ (L),(R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨4,[true,true,false],(rep [true,true] (n)) ++ ([true,true,true,true])⟩ = some ⟨4,([true]) ++ (rep [true,true] (n)) ++ ([true,false]),[true,true,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [] [true,true] [true,true] 2 local1 n [true,false] [true,true,true,true]

theorem phase2 (n : Nat) : run0 table 5 ⟨4,([true]) ++ (rep [true,true] (n)) ++ ([true,false]),[true,true,true,true]⟩ = some ⟨4,([false,true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,false]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨4,([false,true,true,true,true,true]) ++ ([true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true,true,true,true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨4,([false,true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,false]),[]⟩ = some ⟨4,[false,true,true,true,true,true,true,false],(rep [true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true,true,true,true] [] [true,true] [true,true] 6 local3 n [true,false] []

theorem phase4 (n : Nat) : run0 table 16 ⟨4,[false,true,true,true,true,true,true,false],(rep [true,true] (n))⟩ = some ⟨2,[],([true,false,true,true,true,true,true,true]) ++ (rep [true,true] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,true,true,true,true,true]) ++ (rep [true,true] (n)) = ([true,false,true,true]) ++ (rep [true,true] (n)) ++ ([true,true,true,true]) := by
  calc
    _ = ([true,false,true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,false,true,true,true,true,true] [] [true] true n
    _ = ([true,false,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,false,true,true,true,true] [true] [true] true n
    _ = ([true,false,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,false,true,true,true] [true,true] [true] true n
    _ = ([true,false,true,true]) ++ (rep [true,true] (n)) ++ ([true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,false,true,true] [true,true,true] [true] true n

theorem growth (n : Nat) : run0 table (27+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 6+2*n+5+6*n+16=27+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 18 (fun n => 27+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M5837

namespace M5943

-- 1RB1LC_1RC---_0RD1LF_1LD1RE_1LA1RE_0LB0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([false,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true])⟩

theorem entry : run0 table 30 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 3 ⟨1,[],([false,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true])⟩ = some ⟨4,[true,true,false,true],(rep [true,true,true] (n)) ++ ([true,true,true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨4,([true]) ++ (L),([true,true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true,true]) ++ (L),(R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨4,[true,true,false,true],(rep [true,true,true] (n)) ++ ([true,true,true,true])⟩ = some ⟨4,([true]) ++ (rep [true,true,true] (n)) ++ ([true,false,true]),[true,true,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [] [true,true,true] [true,true,true] 3 local1 n [true,false,true] [true,true,true,true]

theorem phase2 (n : Nat) : run0 table 5 ⟨4,([true]) ++ (rep [true,true,true] (n)) ++ ([true,false,true]),[true,true,true,true]⟩ = some ⟨4,([false,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,false,true]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 5 ⟨4,([false,true,true,true,true,true]) ++ ([true,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true,true,true,true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (5*n) ⟨4,([false,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,false,true]),[]⟩ = some ⟨4,[false,true,true,true,true,true,true,false,true],(rep [true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true,true,true,true] [] [true,true,true] [true,true,true] 5 local3 n [true,false,true] []

theorem phase4 (n : Nat) : run0 table 18 ⟨4,[false,true,true,true,true,true,true,false,true],(rep [true,true,true] (n))⟩ = some ⟨1,[],([false,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) = ([false,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true]) := by
  calc
    _ = ([false,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true,true,true] [] [true,true] true n
    _ = ([false,true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true,true] [true] [true,true] true n
    _ = ([false,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true] [true,true] [true,true] true n
    _ = ([false,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true] [true,true,true] [true,true] true n

theorem growth (n : Nat) : run0 table (26+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 3+3*n+5+5*n+18=26+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 30 (fun n => 26+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M5943

namespace M6062

-- 1RB1LF_1RC0LA_0RD---_1LD1RE_1LA1RE_0RB0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true]),[]⟩

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 8 ⟨4,([false,true]) ++ ([true,true,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true]) ++ (L),([true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (8*n) ⟨4,([false,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true]),[]⟩ = some ⟨4,[false,true,true,true,true],(rep [true,true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true] [] [true,true,true,true] [true,true,true,true] 8 local0 n [true,true,true] []

theorem phase1 (n : Nat) : run0 table 19 ⟨4,[false,true,true,true,true],(rep [true,true,true,true] (n))⟩ = some ⟨4,[true,true,true],([true,true,true,true,true]) ++ (rep [true,true,true,true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 4 ⟨4,([true]) ++ (L),([true,true,true,true,true]) ++ ([true,true,true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true,true,true]) ++ (L),([true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (4*n) ⟨4,[true,true,true],([true,true,true,true,true]) ++ (rep [true,true,true,true] (n))⟩ = some ⟨4,([true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true]),[true,true,true,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true,true,true,true,true] [true,true,true,true] [true,true,true,true] 4 local2 n [true,true] []

theorem phase3 (n : Nat) : run0 table 6 ⟨4,([true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true]),[true,true,true,true,true]⟩ = some ⟨4,([false,true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true]) = ([false,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true]) := by
  calc
    _ = ([false,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true] [true,true] [true,true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (25+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 8*n+19+4*n+6=25+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (fun n => 25+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M6062

namespace M6193

-- 1RB1LF_1RC0RB_0RD---_1LD1RE_1LA1RE_0LC1LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,false,2⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true]),[]⟩

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨4,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true]),[]⟩ = some ⟨0,(rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true]),[true]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨0,([true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨0,(L),([true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨0,(rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true]),[true]⟩ = some ⟨0,[true,true,true,true],(rep [true,true,true,true,true,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [] [] [true,true,true,true,true,true] [true,true,true,true,true,true] 6 local1 n [true,true,true,true] [true]

theorem phase2 (n : Nat) : run0 table 5 ⟨0,[true,true,true,true],(rep [true,true,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨1,[true,true],([true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨1,([true]) ++ (L),([true,true,true]) ++ ([true,true,true,true,true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([false,false,false,false,false,false]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨1,[true,true],([true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨1,([true]) ++ (rep [false,false,false,false,false,false] (n)) ++ ([true]),[true,true,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,true,true] [true,true,true,true,true,true] [false,false,false,false,false,false] 6 local3 n [true] [true]

theorem phase4 (n : Nat) : run0 table 18 ⟨1,([true]) ++ (rep [false,false,false,false,false,false] (n)) ++ ([true]),[true,true,true,true]⟩ = some ⟨3,([false,false,false,false,false]) ++ (rep [false,false,false,false,false,false] (n)) ++ ([true]),[true,true,true,true]⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 6 ⟨3,([false,false,false,false,false]) ++ ([false,false,false,false,false,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,false,false]) ++ (L),([true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (6*n) ⟨3,([false,false,false,false,false]) ++ (rep [false,false,false,false,false,false] (n)) ++ ([true]),[true,true,true,true]⟩ = some ⟨3,[false,false,false,false,false,true],(rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,false,false] [] [false,false,false,false,false,false] [true,true,true,true,true,true] 6 local5 n [true] [true,true,true,true]

theorem phase6 (n : Nat) : run0 table 6 ⟨3,[false,false,false,false,false,true],(rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true])⟩ = some ⟨4,[true,true],([true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 6 ⟨4,([true]) ++ (L),([true,true,true,true]) ++ ([true,true,true,true,true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true,true,true,true,true]) ++ (L),([true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (6*n) ⟨4,[true,true],([true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true])⟩ = some ⟨4,([true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[true,true,true,true,true,true,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true,true,true,true] [true,true,true,true,true,true] [true,true,true,true,true,true] 6 local7 n [true] [true,true,true,true]

theorem phase8 (n : Nat) : run0 table 9 ⟨4,([true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[true,true,true,true,true,true,true,true]⟩ = some ⟨4,([false,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]) = ([false,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true]) := by
  calc
    _ = ([false,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true,true,true] [true] [true,true,true,true,true] true n
    _ = ([false,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true,true] [true,true] [true,true,true,true,true] true n
    _ = ([false,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true] [true,true,true] [true,true,true,true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (39+24*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalL n] at H
  rw [show 1+6*n+5+6*n+18+6*n+6+6*n+9=39+24*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (fun n => 39+24*n) entry (by intro n; omega) growth m hm

#print axioms never

end M6193

namespace M6293

-- 1RB1LF_1RC---_0RD0LE_1LD1RE_1LA1RE_0LB1LC

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,2⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,true,false,true]),[]⟩

theorem entry : run0 table 38 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 5 ⟨4,([false,true]) ++ ([true,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (5*n) ⟨4,([false,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,true,false,true]),[]⟩ = some ⟨4,[false,true,true,true,true,true,true,false,true],(rep [true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true] [] [true,true,true] [true,true,true] 5 local0 n [true,true,true,true,true,false,true] []

theorem phase1 (n : Nat) : run0 table 21 ⟨4,[false,true,true,true,true,true,true,false,true],(rep [true,true,true] (n))⟩ = some ⟨4,[true,true,false,true],([true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 3 ⟨4,([true]) ++ (L),([true,true,true,true,true,true,true]) ++ ([true,true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true,true]) ++ (L),([true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (3*n) ⟨4,[true,true,false,true],([true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n))⟩ = some ⟨4,([true]) ++ (rep [true,true,true] (n)) ++ ([true,false,true]),[true,true,true,true,true,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true,true,true,true,true,true,true] [true,true,true] [true,true,true] 3 local2 n [true,false,true] []

theorem phase3 (n : Nat) : run0 table 8 ⟨4,([true]) ++ (rep [true,true,true] (n)) ++ ([true,false,true]),[true,true,true,true,true,true,true]⟩ = some ⟨4,([false,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,false,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,false,true]) = ([false,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,true,false,true]) := by
  calc
    _ = ([false,true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true,true] [true,false,true] [true,true] true n
    _ = ([false,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true] [true,true,false,true] [true,true] true n
    _ = ([false,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true] [true,true,true,false,true] [true,true] true n
    _ = ([false,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,true,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true] [true,true,true,true,false,true] [true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (29+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 5*n+21+3*n+8=29+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 38 (fun n => 29+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M6293

namespace M6700

-- 1RB0LE_1RC0LA_0RD0RF_1LD1RE_1LB1RE_1RB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,true,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 10 ⟨2,([false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]),[]⟩ = some ⟨4,([false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]),[false,true]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨4,([false,true]) ++ ([true,false,true,true,false,true]) ++ (L),(R)⟩ = some ⟨4,([false,true]) ++ (L),([false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨4,([false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]),[false,true]⟩ = some ⟨4,[false,true,true],(rep [false,false,true,false,false,true] (n)) ++ ([false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true] [] [true,false,true,true,false,true] [false,false,true,false,false,true] 6 local1 n [true] [false,true]

theorem phase2 (n : Nat) : run0 table 5 ⟨4,[false,true,true],(rep [false,false,true,false,false,true] (n)) ++ ([false,true])⟩ = some ⟨2,[true,true],([false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([false,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨2,([true]) ++ (L),([false,false,true]) ++ ([false,false,true,false,false,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true,false,true,true,false]) ++ (L),([false,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨2,[true,true],([false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([false,true])⟩ = some ⟨2,([true]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),[false,false,true,false,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,false,true] [false,false,true,false,false,true] [true,true,false,true,true,false] 6 local3 n [true] [false,true]

theorem phase4 (n : Nat) : run0 table 5 ⟨2,([true]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),[false,false,true,false,true]⟩ = some ⟨1,([true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 6 ⟨1,([true,true,false,true,true,false]) ++ ([true,true,false,true,true,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,true,true,false]) ++ (L),([true,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (6*n) ⟨1,([true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),[]⟩ = some ⟨1,[true,true,false,true,true,false,true],(rep [true,false,false,true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,true,true,false] [] [true,true,false,true,true,false] [true,false,false,true,false,false] 6 local5 n [true] []

theorem phase6 (n : Nat) : run0 table 8 ⟨1,[true,true,false,true,true,false,true],(rep [true,false,false,true,false,false] (n))⟩ = some ⟨1,[false,true],([true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n))⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 6 ⟨1,([false]) ++ (L),([true,false,false,true,false,false]) ++ ([true,false,false,true,false,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,false,true,true,false,true]) ++ (L),([true,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (6*n) ⟨1,[false,true],([true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n))⟩ = some ⟨1,([false]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]),[true,false,false,true,false,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,false,false,true,false,false] [true,false,false,true,false,false] [true,false,true,true,false,true] 6 local7 n [true] []

theorem phase8 (n : Nat) : run0 table 7 ⟨1,([false]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]),[true,false,false,true,false,false]⟩ = some ⟨2,([false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]) = ([false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (35+24*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 10+6*n+5+6*n+5+6*n+8+6*n+7=35+24*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 35+24*n) entry (by intro n; omega) growth m hm

#print axioms never

end M6700

namespace M6704

-- 1RB0LF_1RC0LA_0RD1RB_1LD1RE_1LB1RE_---0LD

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨1,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ = some ⟨4,([false,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 10 ⟨4,([false,true,true,true]) ++ ([true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true,true]) ++ (L),([false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (10*n) ⟨4,([false,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ = some ⟨4,[false,true,true,true,true],(rep [false,false,true,false,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true,true] [] [true,true,true,true,true,true] [false,false,true,false,false,true] 10 local1 n [true] []

theorem phase2 (n : Nat) : run0 table 8 ⟨4,[false,true,true,true,true],(rep [false,false,true,false,false,true] (n))⟩ = some ⟨1,[false,true],([true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 10 ⟨1,([false]) ++ (L),([true,false,false,true]) ++ ([false,false,true,false,false,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,true,true,true,true,true]) ++ (L),([true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (10*n) ⟨1,[false,true],([true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n))⟩ = some ⟨1,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[true,false,false,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,false,false,true] [false,false,true,false,false,true] [true,true,true,true,true,true] 10 local3 n [true] []

theorem phase4 (n : Nat) : run0 table 10 ⟨1,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[true,false,false,true]⟩ = some ⟨1,([false,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]) = ([false,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (25+20*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 7+10*n+8+10*n+10=25+20*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 25+20*n) entry (by intro n; omega) growth m hm

#print axioms never

end M6704

namespace M6706

-- 1RB0LF_1RC0LA_0RD1RB_1LD1RE_1LB1RE_---0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨1,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ = some ⟨4,([false,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 10 ⟨4,([false,true,true,true]) ++ ([true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true,true]) ++ (L),([false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (10*n) ⟨4,([false,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ = some ⟨4,[false,true,true,true,true],(rep [false,false,true,false,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true,true] [] [true,true,true,true,true,true] [false,false,true,false,false,true] 10 local1 n [true] []

theorem phase2 (n : Nat) : run0 table 8 ⟨4,[false,true,true,true,true],(rep [false,false,true,false,false,true] (n))⟩ = some ⟨1,[false,true],([true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 10 ⟨1,([false]) ++ (L),([true,false,false,true]) ++ ([false,false,true,false,false,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,true,true,true,true,true]) ++ (L),([true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (10*n) ⟨1,[false,true],([true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n))⟩ = some ⟨1,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[true,false,false,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,false,false,true] [false,false,true,false,false,true] [true,true,true,true,true,true] 10 local3 n [true] []

theorem phase4 (n : Nat) : run0 table 10 ⟨1,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[true,false,false,true]⟩ = some ⟨1,([false,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]) = ([false,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (25+20*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 7+10*n+8+10*n+10=25+20*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 25+20*n) entry (by intro n; omega) growth m hm

#print axioms never

end M6706

namespace M6710

-- 1RB0LF_1RC0LA_0RD1RB_1LD1RE_1LB1RE_---1LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 8 ⟨1,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ = some ⟨1,([true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[true]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨1,([true,true,true]) ++ ([true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨1,([true,true,true]) ++ (L),([true,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨1,([true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[true]⟩ = some ⟨1,[true,true,true,true],(rep [true,false,false,true,false,false] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,true] [] [true,true,true,true,true,true] [true,false,false,true,false,false] 6 local1 n [true] [true]

theorem phase2 (n : Nat) : run0 table 5 ⟨1,[true,true,true,true],(rep [true,false,false,true,false,false] (n)) ++ ([true])⟩ = some ⟨1,[false,true],([true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 10 ⟨1,([false]) ++ (L),([true,false,false]) ++ ([true,false,false,true,false,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,true,true,true,true,true]) ++ (L),([true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (10*n) ⟨1,[false,true],([true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true])⟩ = some ⟨1,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[true,false,false,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,false,false] [true,false,false,true,false,false] [true,true,true,true,true,true] 10 local3 n [true] [true]

theorem phase4 (n : Nat) : run0 table 10 ⟨1,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[true,false,false,true]⟩ = some ⟨1,([false,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]) = ([false,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (23+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 8+6*n+5+10*n+10=23+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 23+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M6710

namespace M6746

-- 1RB1LE_1RC0LA_0RD0RF_1LD1RE_1LB1RE_---1RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true,true]) ++ (rep [false,true,true,false,true,true] (n)),[]⟩

theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 16 ⟨2,([false,true,true]) ++ (rep [false,true,true,false,true,true] (n)),[]⟩ = some ⟨4,([false,true,true]) ++ (rep [false,true,true,false,true,true] (n)),[true,true]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨4,([false,true,true]) ++ ([false,true,true,false,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨4,([false,true,true]) ++ (rep [false,true,true,false,true,true] (n)),[true,true]⟩ = some ⟨4,[false,true,true],(rep [true,false,true,true,false,true] (n)) ++ ([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true] [] [false,true,true,false,true,true] [true,false,true,true,false,true] 6 local1 n [] [true,true]

theorem phase2 (n : Nat) : run0 table 5 ⟨4,[false,true,true],(rep [true,false,true,true,false,true] (n)) ++ ([true,true])⟩ = some ⟨2,[true,true],([true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨2,([true]) ++ (L),([true,false,true]) ++ ([true,false,true,true,false,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true,false,true,true,false]) ++ (L),([true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨2,[true,true],([true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true,true])⟩ = some ⟨2,([true]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),[true,false,true,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true,false,true] [true,false,true,true,false,true] [true,true,false,true,true,false] 6 local3 n [true] [true,true]

theorem phase4 (n : Nat) : run0 table 5 ⟨2,([true]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),[true,false,true,true,true]⟩ = some ⟨1,([true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 6 ⟨1,([true,true,false,true,true,false]) ++ ([true,true,false,true,true,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,true,true,false]) ++ (L),([true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (6*n) ⟨1,([true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),[]⟩ = some ⟨1,[true,true,false,true,true,false,true],(rep [true,true,false,true,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,true,true,false] [] [true,true,false,true,true,false] [true,true,false,true,true,false] 6 local5 n [true] []

theorem phase6 (n : Nat) : run0 table 8 ⟨1,[true,true,false,true,true,false,true],(rep [true,true,false,true,true,false] (n))⟩ = some ⟨1,[false,true],([true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n))⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 6 ⟨1,([false]) ++ (L),([true,true,false,true,true,false]) ++ ([true,true,false,true,true,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,false,true,true,false,true]) ++ (L),([true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (6*n) ⟨1,[false,true],([true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n))⟩ = some ⟨1,([false]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]),[true,true,false,true,true,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,true,false,true,true,false] [true,true,false,true,true,false] [true,false,true,true,false,true] 6 local7 n [true] []

theorem phase8 (n : Nat) : run0 table 7 ⟨1,([false]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]),[true,true,false,true,true,false]⟩ = some ⟨2,([false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]) = ([false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) := by
  calc
    _ = ([false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,false,true,true,false,true] [] [false,true,true,false,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (41+24*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalL n] at H
  rw [show 16+6*n+5+6*n+5+6*n+8+6*n+7=41+24*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 41+24*n) entry (by intro n; omega) growth m hm

#print axioms never

end M6746

namespace M6919

-- 1RB---_1RC0LE_0RD0RF_1LD1RE_1LB1RE_1LF0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨2,([false,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ = some ⟨4,([false,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 18 ⟨4,([false,true,true,true]) ++ ([true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true,true]) ++ (L),([true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (18*n) ⟨4,([false,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ = some ⟨4,[false,true,true,true,true],(rep [true,true,true,true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true,true] [] [true,true,true,true,true,true] [true,true,true,true,true,true] 18 local1 n [true] []

theorem phase2 (n : Nat) : run0 table 18 ⟨4,[false,true,true,true,true],(rep [true,true,true,true,true,true] (n))⟩ = some ⟨1,[false,true],([true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 12 ⟨1,([false]) ++ (L),([true,true,true,true,true,true]) ++ ([true,true,true,true,true,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (12*n) ⟨1,[false,true],([true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n))⟩ = some ⟨1,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[true,true,true,true,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,true,true,true,true,true] [true,true,true,true,true,true] [true,true,true,true,true,true] 12 local3 n [true] []

theorem phase4 (n : Nat) : run0 table 13 ⟨1,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[true,true,true,true,true,true]⟩ = some ⟨2,([false,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]) = ([false,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (37+30*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 6+18*n+18+12*n+13=37+30*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 37+30*n) entry (by intro n; omega) growth m hm

#print axioms never

end M6919

namespace M7034

-- 1RB1LA_1RC0LF_0RD---_1LD1RE_1LB1RE_0RF0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨2,([false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]),[]⟩ = some ⟨1,([true,true,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]),[true]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 10 ⟨1,([true,true,true]) ++ ([true,false,true,true,false,true]) ++ (L),(R)⟩ = some ⟨1,([true,true,true]) ++ (L),([true,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (10*n) ⟨1,([true,true,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]),[true]⟩ = some ⟨1,[true,true,true,true],(rep [true,false,false,true,false,false] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,true] [] [true,false,true,true,false,true] [true,false,false,true,false,false] 10 local1 n [true] [true]

theorem phase2 (n : Nat) : run0 table 8 ⟨1,[true,true,true,true],(rep [true,false,false,true,false,false] (n)) ++ ([true])⟩ = some ⟨1,[false,true],([false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 18 ⟨1,([false]) ++ (L),([false,true,false,false]) ++ ([true,false,false,true,false,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,false,true,true,false,true]) ++ (L),([false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (18*n) ⟨1,[false,true],([false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true])⟩ = some ⟨1,([false]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]),[false,true,false,false,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [false,true,false,false] [true,false,false,true,false,false] [true,false,true,true,false,true] 18 local3 n [true] [true]

theorem phase4 (n : Nat) : run0 table 19 ⟨1,([false]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]),[false,true,false,false,true]⟩ = some ⟨2,([false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]) = ([false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (34+28*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 7+10*n+8+18*n+19=34+28*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 34+28*n) entry (by intro n; omega) growth m hm

#print axioms never

end M7034

namespace M7063

-- 1RB---_1RC0LF_0RD0RA_1LD1RE_1LB1RE_0LE0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],(rep [false,false,true,false,false,true,false,false,true] (n)) ++ ([false,false,true,false,true])⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨4,[],(rep [false,false,true,false,false,true,false,false,true] (n)) ++ ([false,false,true,false,true])⟩ = some ⟨2,[true,true],(rep [false,false,true,false,false,true,false,false,true] (n)) ++ ([false,false,true,false,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 9 ⟨2,([true]) ++ (L),([false,false,true,false,false,true,false,false,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true,false,true,true,false,true,true,false]) ++ (L),(R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (9*n) ⟨2,[true,true],(rep [false,false,true,false,false,true,false,false,true] (n)) ++ ([false,false,true,false,true])⟩ = some ⟨2,([true]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true]),[false,false,true,false,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [] [false,false,true,false,false,true,false,false,true] [true,true,false,true,true,false,true,true,false] 9 local1 n [true] [false,false,true,false,true]

theorem phase2 (n : Nat) : run0 table 5 ⟨2,([true]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true]),[false,false,true,false,true]⟩ = some ⟨1,([true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 9 ⟨1,([true,true,false,true,true,false]) ++ ([true,true,false,true,true,false,true,true,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,true,true,false]) ++ (L),([true,false,false,true,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (9*n) ⟨1,([true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true]),[]⟩ = some ⟨1,[true,true,false,true,true,false,true],(rep [true,false,false,true,false,false,true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,true,true,false] [] [true,true,false,true,true,false,true,true,false] [true,false,false,true,false,false,true,false,false] 9 local3 n [true] []

theorem phase4 (n : Nat) : run0 table 10 ⟨1,[true,true,false,true,true,false,true],(rep [true,false,false,true,false,false,true,false,false] (n))⟩ = some ⟨2,[true,true],([false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n))⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 9 ⟨2,([true]) ++ (L),([false,false,true,false,false,true,false,false]) ++ ([true,false,false,true,false,false,true,false,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true,false,true,true,false,true,true,false]) ++ (L),([false,false,true,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (9*n) ⟨2,[true,true],([false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n))⟩ = some ⟨2,([true]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true]),[false,false,true,false,false,true,false,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,false,true,false,false,true,false,false] [true,false,false,true,false,false,true,false,false] [true,true,false,true,true,false,true,true,false] 9 local5 n [true] []

theorem phase6 (n : Nat) : run0 table 19 ⟨2,([true]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true]),[false,false,true,false,false,true,false,false]⟩ = some ⟨4,([false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true]),[false,true]⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 9 ⟨4,([false,true,true,false,true,true,false,true,true,false]) ++ ([true,true,false,true,true,false,true,true,false]) ++ (L),(R)⟩ = some ⟨4,([false,true,true,false,true,true,false,true,true,false]) ++ (L),([false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (9*n) ⟨4,([false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true]),[false,true]⟩ = some ⟨4,[false,true,true,false,true,true,false,true,true,false,true],(rep [false,false,true,false,false,true,false,false,true] (n)) ++ ([false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true,false,true,true,false,true,true,false] [] [true,true,false,true,true,false,true,true,false] [false,false,true,false,false,true,false,false,true] 9 local7 n [true] [false,true]

theorem phase8 (n : Nat) : run0 table 12 ⟨4,[false,true,true,false,true,true,false,true,true,false,true],(rep [false,false,true,false,false,true,false,false,true] (n)) ++ ([false,true])⟩ = some ⟨4,[],([false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) ++ ([false,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) ++ ([false,true]) = ([false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) ++ ([false,false,true,false,true]) := by
  calc
    _ = ([false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,false,true,false,false,true,false,false,true,false,false] [false,true] [false,false,true,false,false,true,false,false] true n
    _ = ([false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false,true,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,false,true,false,false,true,false,false,true,false] [true,false,true] [true,false,false,true,false,false,true,false] false n
    _ = ([false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) ++ ([false,false,true,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,false,true,false,false,true,false,false,true] [false,true,false,true] [false,true,false,false,true,false,false,true] false n

theorem growth (n : Nat) : run0 table (48+36*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalR n] at H
  rw [show 2+9*n+5+9*n+10+9*n+19+9*n+12=48+36*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 15 (fun n => 48+36*n) entry (by intro n; omega) growth m hm

#print axioms never

end M7063

namespace M7064

-- 1RB---_1RC0LF_0RD0RA_1LD1RE_1LB1RE_0RB0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,false]),[]⟩

theorem entry : run0 table 37 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 10 ⟨2,([false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,false]),[]⟩ = some ⟨4,([false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,false]),[false,true]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨4,([false,true]) ++ ([true,false,true]) ++ (L),(R)⟩ = some ⟨4,([false,true]) ++ (L),([false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨4,([false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,false]),[false,true]⟩ = some ⟨4,[false,true,true,false,true,true,false,true,false],(rep [false,false,true] (n)) ++ ([false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true] [] [true,false,true] [false,false,true] 3 local1 n [true,false,true,true,false,true,false] [false,true]

theorem phase2 (n : Nat) : run0 table 9 ⟨4,[false,true,true,false,true,true,false,true,false],(rep [false,false,true] (n)) ++ ([false,true])⟩ = some ⟨1,[false,false],([true,false,false,true,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([false,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([false]) ++ (L),([true,false,false,true,false,false,true]) ++ ([false,false,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,false,true]) ++ (L),([true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,[false,false],([true,false,false,true,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([false,true])⟩ = some ⟨1,([false]) ++ (rep [true,false,true] (n)) ++ ([false]),[true,false,false,true,false,false,true,false,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,false,false,true,false,false,true] [false,false,true] [true,false,true] 3 local3 n [false] [false,true]

theorem phase4 (n : Nat) : run0 table 9 ⟨1,([false]) ++ (rep [true,false,true] (n)) ++ ([false]),[true,false,false,true,false,false,true,false,true]⟩ = some ⟨1,([true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([false]),[]⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 3 ⟨1,([true,true,false,true,true,false,true,true,false,true]) ++ ([true,false,true]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,true,true,false,true,true,false,true]) ++ (L),([true,false,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (3*n) ⟨1,([true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([false]),[]⟩ = some ⟨1,[true,true,false,true,true,false,true,true,false,true,false],(rep [true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,true,true,false,true,true,false,true] [] [true,false,true] [true,false,false] 3 local5 n [false] []

theorem phase6 (n : Nat) : run0 table 11 ⟨1,[true,true,false,true,true,false,true,true,false,true,false],(rep [true,false,false] (n))⟩ = some ⟨1,[false,false],([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n))⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 3 ⟨1,([false]) ++ (L),([true,false,false,true,false,false,true,false,false]) ++ ([true,false,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,false,true]) ++ (L),([true,false,false,true,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (3*n) ⟨1,[false,false],([true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false] (n))⟩ = some ⟨1,([false]) ++ (rep [true,false,true] (n)) ++ ([false]),[true,false,false,true,false,false,true,false,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,false,false,true,false,false,true,false,false] [true,false,false] [true,false,true] 3 local7 n [false] []

theorem phase8 (n : Nat) : run0 table 10 ⟨1,([false]) ++ (rep [true,false,true] (n)) ++ ([false]),[true,false,false,true,false,false,true,false,false]⟩ = some ⟨2,([false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([false]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([false]) = ([false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,false]) := by
  calc
    _ = ([false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,false,true,true,false,true,true,false] [false] [true,false] true n
    _ = ([false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,false,true,true,false,true,true] [true,false] [true,true] false n
    _ = ([false,true,true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,false,true,true,false,true] [false,true,false] [false,true] true n
    _ = ([false,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true,true,false,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,false,true,true,false] [true,false,true,false] [true,false] true n
    _ = ([false,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,false,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,false,true,true] [true,true,false,true,false] [true,true] false n
    _ = ([false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,false,true] [false,true,true,false,true,false] [false,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (49+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalL n] at H
  rw [show 10+3*n+9+3*n+9+3*n+11+3*n+10=49+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 37 (fun n => 49+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M7064

namespace M7066

-- 1RB---_1RC0LF_0RD0RA_1LD1RE_1LB1RE_1RB0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,true,1⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 10 ⟨2,([false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]),[]⟩ = some ⟨4,([false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]),[false,true]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨4,([false,true]) ++ ([true,false,true,true,false,true]) ++ (L),(R)⟩ = some ⟨4,([false,true]) ++ (L),([false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨4,([false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]),[false,true]⟩ = some ⟨4,[false,true,true],(rep [false,false,true,false,false,true] (n)) ++ ([false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true] [] [true,false,true,true,false,true] [false,false,true,false,false,true] 6 local1 n [true] [false,true]

theorem phase2 (n : Nat) : run0 table 5 ⟨4,[false,true,true],(rep [false,false,true,false,false,true] (n)) ++ ([false,true])⟩ = some ⟨2,[true,true],([false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([false,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨2,([true]) ++ (L),([false,false,true]) ++ ([false,false,true,false,false,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true,false,true,true,false]) ++ (L),([false,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨2,[true,true],([false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([false,true])⟩ = some ⟨2,([true]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),[false,false,true,false,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,false,true] [false,false,true,false,false,true] [true,true,false,true,true,false] 6 local3 n [true] [false,true]

theorem phase4 (n : Nat) : run0 table 5 ⟨2,([true]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),[false,false,true,false,true]⟩ = some ⟨1,([true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 6 ⟨1,([true,true,false,true,true,false]) ++ ([true,true,false,true,true,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,true,true,false]) ++ (L),([true,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (6*n) ⟨1,([true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false] (n)) ++ ([true]),[]⟩ = some ⟨1,[true,true,false,true,true,false,true],(rep [true,false,false,true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,true,true,false] [] [true,true,false,true,true,false] [true,false,false,true,false,false] 6 local5 n [true] []

theorem phase6 (n : Nat) : run0 table 8 ⟨1,[true,true,false,true,true,false,true],(rep [true,false,false,true,false,false] (n))⟩ = some ⟨1,[false,true],([true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n))⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 6 ⟨1,([false]) ++ (L),([true,false,false,true,false,false]) ++ ([true,false,false,true,false,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,false,true,true,false,true]) ++ (L),([true,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (6*n) ⟨1,[false,true],([true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n))⟩ = some ⟨1,([false]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]),[true,false,false,true,false,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,false,false,true,false,false] [true,false,false,true,false,false] [true,false,true,true,false,true] 6 local7 n [true] []

theorem phase8 (n : Nat) : run0 table 7 ⟨1,([false]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]),[true,false,false,true,false,false]⟩ = some ⟨2,([false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]) = ([false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (35+24*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 10+6*n+5+6*n+5+6*n+8+6*n+7=35+24*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 35+24*n) entry (by intro n; omega) growth m hm

#print axioms never

end M7066

namespace M7067

-- 1RB---_1RC0LF_0RD0RA_1LD1RE_1LB1RE_1RF0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,true,5⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],(rep [false,false,true,false,false,true,false,false,true] (n)) ++ ([false,false,true,false,true])⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨4,[],(rep [false,false,true,false,false,true,false,false,true] (n)) ++ ([false,false,true,false,true])⟩ = some ⟨2,[true,true],(rep [false,false,true,false,false,true,false,false,true] (n)) ++ ([false,false,true,false,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 9 ⟨2,([true]) ++ (L),([false,false,true,false,false,true,false,false,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true,false,true,true,false,true,true,false]) ++ (L),(R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (9*n) ⟨2,[true,true],(rep [false,false,true,false,false,true,false,false,true] (n)) ++ ([false,false,true,false,true])⟩ = some ⟨2,([true]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true]),[false,false,true,false,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [] [false,false,true,false,false,true,false,false,true] [true,true,false,true,true,false,true,true,false] 9 local1 n [true] [false,false,true,false,true]

theorem phase2 (n : Nat) : run0 table 5 ⟨2,([true]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true]),[false,false,true,false,true]⟩ = some ⟨1,([true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 9 ⟨1,([true,true,false,true,true,false]) ++ ([true,true,false,true,true,false,true,true,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,true,true,false]) ++ (L),([true,false,false,true,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (9*n) ⟨1,([true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true]),[]⟩ = some ⟨1,[true,true,false,true,true,false,true],(rep [true,false,false,true,false,false,true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,true,true,false] [] [true,true,false,true,true,false,true,true,false] [true,false,false,true,false,false,true,false,false] 9 local3 n [true] []

theorem phase4 (n : Nat) : run0 table 16 ⟨1,[true,true,false,true,true,false,true],(rep [true,false,false,true,false,false,true,false,false] (n))⟩ = some ⟨2,[true,true],([false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n))⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 9 ⟨2,([true]) ++ (L),([false,false,true,false,false,true,false,false]) ++ ([true,false,false,true,false,false,true,false,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true,false,true,true,false,true,true,false]) ++ (L),([false,false,true,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (9*n) ⟨2,[true,true],([false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n))⟩ = some ⟨2,([true]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true]),[false,false,true,false,false,true,false,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,false,true,false,false,true,false,false] [true,false,false,true,false,false,true,false,false] [true,true,false,true,true,false,true,true,false] 9 local5 n [true] []

theorem phase6 (n : Nat) : run0 table 19 ⟨2,([true]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true]),[false,false,true,false,false,true,false,false]⟩ = some ⟨4,([false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true]),[false,true]⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 9 ⟨4,([false,true,true,false,true,true,false,true,true,false]) ++ ([true,true,false,true,true,false,true,true,false]) ++ (L),(R)⟩ = some ⟨4,([false,true,true,false,true,true,false,true,true,false]) ++ (L),([false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (9*n) ⟨4,([false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true]),[false,true]⟩ = some ⟨4,[false,true,true,false,true,true,false,true,true,false,true],(rep [false,false,true,false,false,true,false,false,true] (n)) ++ ([false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true,false,true,true,false,true,true,false] [] [true,true,false,true,true,false,true,true,false] [false,false,true,false,false,true,false,false,true] 9 local7 n [true] [false,true]

theorem phase8 (n : Nat) : run0 table 18 ⟨4,[false,true,true,false,true,true,false,true,true,false,true],(rep [false,false,true,false,false,true,false,false,true] (n)) ++ ([false,true])⟩ = some ⟨4,[],([false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) ++ ([false,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) ++ ([false,true]) = ([false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) ++ ([false,false,true,false,true]) := by
  calc
    _ = ([false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) ++ ([true,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,false,true,false,false,true,false,false,true,false,false] [false,true] [false,false,true,false,false,true,false,false] true n
    _ = ([false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false,true,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,false,true,false,false,true,false,false,true,false] [true,false,true] [true,false,false,true,false,false,true,false] false n
    _ = ([false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true] (n)) ++ ([false,false,true,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,false,true,false,false,true,false,false,true] [false,true,false,true] [false,true,false,false,true,false,false,true] false n

theorem growth (n : Nat) : run0 table (60+36*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalR n] at H
  rw [show 2+9*n+5+9*n+16+9*n+19+9*n+18=60+36*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 15 (fun n => 60+36*n) entry (by intro n; omega) growth m hm

#print axioms never

end M7067

namespace M7120

-- 1RB0LA_1RC0LF_0RD---_1LD1RE_1LB1RE_0RC1LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false,true,true]) ++ (rep [false,false] (n)) ++ ([true,true]),[]⟩

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨4,([false,true,true]) ++ (rep [false,false] (n)) ++ ([true,true]),[]⟩ = some ⟨1,([true,true]) ++ (rep [false,false] (n)) ++ ([true,true]),[true]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨1,([true,true]) ++ ([false,false]) ++ (L),(R)⟩ = some ⟨1,([true,true]) ++ (L),([false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨1,([true,true]) ++ (rep [false,false] (n)) ++ ([true,true]),[true]⟩ = some ⟨1,[true,true,true,true],(rep [false,false] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true] [] [false,false] [false,false] 6 local1 n [true,true] [true]

theorem phase2 (n : Nat) : run0 table 6 ⟨1,[true,true,true,true],(rep [false,false] (n)) ++ ([true])⟩ = some ⟨2,[false,true,true],([true,false]) ++ (rep [false,false] (n)) ++ ([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 10 ⟨2,([false]) ++ (L),([true,false]) ++ ([false,false]) ++ (R)⟩ = some ⟨2,([false]) ++ ([false,false]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (10*n) ⟨2,[false,true,true],([true,false]) ++ (rep [false,false] (n)) ++ ([true])⟩ = some ⟨2,([false]) ++ (rep [false,false] (n)) ++ ([true,true]),[true,false,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false] [false,false] [false,false] 10 local3 n [true,true] [true]

theorem phase4 (n : Nat) : run0 table 8 ⟨2,([false]) ++ (rep [false,false] (n)) ++ ([true,true]),[true,false,true]⟩ = some ⟨4,([false,true,true,false,false]) ++ (rep [false,false] (n)) ++ ([true,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,false,false]) ++ (rep [false,false] (n)) ++ ([true,true]) = ([false,true,true,false,false]) ++ (rep [false,false] (n)) ++ ([true,true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (15+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 1+6*n+6+10*n+8=15+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (fun n => 15+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M7120

namespace M8089

-- 1RB1LE_1RC1LF_0RD0RD_1LD1RE_1LB1RE_---0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false,true,true]) ++ (rep [true,true] (n)) ++ ([true,false,true,true,true,true]),[]⟩

theorem entry : run0 table 44 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 6 ⟨4,([false,true,true]) ++ ([true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (6*n) ⟨4,([false,true,true]) ++ (rep [true,true] (n)) ++ ([true,false,true,true,true,true]),[]⟩ = some ⟨4,[false,true,true,true,false,true,true,true,true],(rep [true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true] [] [true,true] [true,true] 6 local0 n [true,false,true,true,true,true] []

theorem phase1 (n : Nat) : run0 table 33 ⟨4,[false,true,true,true,false,true,true,true,true],(rep [true,true] (n))⟩ = some ⟨4,[true,true,false,true,true,true,true],([true,true,true]) ++ (rep [true,true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 2 ⟨4,([true]) ++ (L),([true,true,true]) ++ ([true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (2*n) ⟨4,[true,true,false,true,true,true,true],([true,true,true]) ++ (rep [true,true] (n))⟩ = some ⟨4,([true]) ++ (rep [true,true] (n)) ++ ([true,false,true,true,true,true]),[true,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true,true,true] [true,true] [true,true] 2 local2 n [true,false,true,true,true,true] []

theorem phase3 (n : Nat) : run0 table 4 ⟨4,([true]) ++ (rep [true,true] (n)) ++ ([true,false,true,true,true,true]),[true,true,true]⟩ = some ⟨4,([false,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,false,true,true,true,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,false,true,true,true,true]) = ([false,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,false,true,true,true,true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (37+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [show 6*n+33+2*n+4=37+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 44 (fun n => 37+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M8089

namespace M8090

-- 1RB1LE_1RC1LF_0RD0RE_1LD1RE_1LB1RE_---0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false,true,true]) ++ (rep [true,true] (n)) ++ ([true,false,true,true,true,true]),[]⟩

theorem entry : run0 table 44 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 6 ⟨4,([false,true,true]) ++ ([true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (6*n) ⟨4,([false,true,true]) ++ (rep [true,true] (n)) ++ ([true,false,true,true,true,true]),[]⟩ = some ⟨4,[false,true,true,true,false,true,true,true,true],(rep [true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true] [] [true,true] [true,true] 6 local0 n [true,false,true,true,true,true] []

theorem phase1 (n : Nat) : run0 table 32 ⟨4,[false,true,true,true,false,true,true,true,true],(rep [true,true] (n))⟩ = some ⟨4,[true,false,true,true,true,true],([true,true,true,true]) ++ (rep [true,true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 2 ⟨4,([true]) ++ (L),([true,true,true,true]) ++ ([true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true]) ++ (L),([true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (2*n) ⟨4,[true,false,true,true,true,true],([true,true,true,true]) ++ (rep [true,true] (n))⟩ = some ⟨4,([true]) ++ (rep [true,true] (n)) ++ ([false,true,true,true,true]),[true,true,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true,true,true,true] [true,true] [true,true] 2 local2 n [false,true,true,true,true] []

theorem phase3 (n : Nat) : run0 table 5 ⟨4,([true]) ++ (rep [true,true] (n)) ++ ([false,true,true,true,true]),[true,true,true,true]⟩ = some ⟨4,([false,true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false,true,true,true,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false,true,true,true,true]) = ([false,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,false,true,true,true,true]) := by
  calc
    _ = ([false,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,false,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true] [false,true,true,true,true] [true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (37+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 6*n+32+2*n+5=37+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 44 (fun n => 37+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M8090

namespace M8837

-- 1RB0LF_1RC---_0RD0RA_1LD1RE_1LC1RE_0LA1LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([false]) ++ (rep [true,false] (n)) ++ ([true,false,false,false])⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨5,[],([false]) ++ (rep [true,false] (n)) ++ ([true,false,false,false])⟩ = some ⟨1,[false,true],([false]) ++ (rep [true,false] (n)) ++ ([true,false,false,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 8 ⟨1,([false]) ++ (L),([false]) ++ ([true,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,true]) ++ (L),([false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (8*n) ⟨1,[false,true],([false]) ++ (rep [true,false] (n)) ++ ([true,false,false,false])⟩ = some ⟨1,([false]) ++ (rep [true,true] (n)) ++ ([true]),[false,true,false,false,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [false] [true,false] [true,true] 8 local1 n [true] [true,false,false,false]

theorem phase2 (n : Nat) : run0 table 19 ⟨1,([false]) ++ (rep [true,true] (n)) ++ ([true]),[false,true,false,false,false]⟩ = some ⟨0,([true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true]),[false,false]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 2 ⟨0,([true,true,true,true]) ++ ([true,true]) ++ (L),(R)⟩ = some ⟨0,([true,true,true,true]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (2*n) ⟨0,([true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true]),[false,false]⟩ = some ⟨0,[true,true,true,true,true],(rep [true,false] (n)) ++ ([false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,true,true,true] [] [true,true] [true,false] 2 local3 n [true] [false,false]

theorem phase4 (n : Nat) : run0 table 5 ⟨0,[true,true,true,true,true],(rep [true,false] (n)) ++ ([false,false])⟩ = some ⟨5,[],([false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([false,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([false,false]) = ([false,true,false]) ++ (rep [true,false] (n)) ++ ([true,false,false,false]) := by
  calc
    _ = ([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([false,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,false,true] [false,false] [true] false n
    _ = ([false,true,false]) ++ (rep [true,false] (n)) ++ ([true,false,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,false] [false,false,false] [false] true n

theorem growth (n : Nat) : run0 table (26+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 2+8*n+19+2*n+5=26+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 15 (fun n => 26+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M8837

namespace M8998

-- 1RB1LF_1RC0LB_0RD1LA_1LD1RE_1LC1RE_---0LD

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true]),[]⟩

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 5 ⟨4,([false,true]) ++ ([true,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (5*n) ⟨4,([false,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true]),[]⟩ = some ⟨4,[false,true,true,true,true],(rep [true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true] [] [true,true,true] [true,true,true] 5 local0 n [true,true,true] []

theorem phase1 (n : Nat) : run0 table 15 ⟨4,[false,true,true,true,true],(rep [true,true,true] (n))⟩ = some ⟨4,[true,true],([true,true,true,true,true]) ++ (rep [true,true,true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 3 ⟨4,([true]) ++ (L),([true,true,true,true,true]) ++ ([true,true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true,true]) ++ (L),([true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (3*n) ⟨4,[true,true],([true,true,true,true,true]) ++ (rep [true,true,true] (n))⟩ = some ⟨4,([true]) ++ (rep [true,true,true] (n)) ++ ([true]),[true,true,true,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true,true,true,true,true] [true,true,true] [true,true,true] 3 local2 n [true] []

theorem phase3 (n : Nat) : run0 table 6 ⟨4,([true]) ++ (rep [true,true,true] (n)) ++ ([true]),[true,true,true,true,true]⟩ = some ⟨4,([false,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]) = ([false,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true]) := by
  calc
    _ = ([false,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true] [true] [true,true] true n
    _ = ([false,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true] [true,true] [true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (21+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 5*n+15+3*n+6=21+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (fun n => 21+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M8998

namespace M8999

-- 1RB1LF_1RC0LB_0RD1LA_1LD1RE_1LC1RE_---0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true]),[]⟩

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 5 ⟨4,([false,true]) ++ ([true,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (5*n) ⟨4,([false,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true]),[]⟩ = some ⟨4,[false,true,true,true,true],(rep [true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true] [] [true,true,true] [true,true,true] 5 local0 n [true,true,true] []

theorem phase1 (n : Nat) : run0 table 15 ⟨4,[false,true,true,true,true],(rep [true,true,true] (n))⟩ = some ⟨4,[true,true],([true,true,true,true,true]) ++ (rep [true,true,true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 3 ⟨4,([true]) ++ (L),([true,true,true,true,true]) ++ ([true,true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true,true]) ++ (L),([true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (3*n) ⟨4,[true,true],([true,true,true,true,true]) ++ (rep [true,true,true] (n))⟩ = some ⟨4,([true]) ++ (rep [true,true,true] (n)) ++ ([true]),[true,true,true,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true,true,true,true,true] [true,true,true] [true,true,true] 3 local2 n [true] []

theorem phase3 (n : Nat) : run0 table 6 ⟨4,([true]) ++ (rep [true,true,true] (n)) ++ ([true]),[true,true,true,true,true]⟩ = some ⟨4,([false,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]) = ([false,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true]) := by
  calc
    _ = ([false,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true] [true] [true,true] true n
    _ = ([false,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true] [true,true] [true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (21+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 5*n+15+3*n+6=21+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (fun n => 21+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M8999

namespace M9002

-- 1RB1LF_1RC1RB_0RD1LA_1LD1RE_1LC1RE_---0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true]),[]⟩

theorem entry : run0 table 21 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨1,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true]),[]⟩ = some ⟨4,([false,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true]),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 10 ⟨4,([false,true,true,true]) ++ ([true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true,true]) ++ (L),([true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (10*n) ⟨4,([false,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true]),[]⟩ = some ⟨4,[false,true,true,true,true,true,true,true,true,true],(rep [true,true,true,true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true,true] [] [true,true,true,true,true,true] [true,true,true,true,true,true] 10 local1 n [true,true,true,true,true,true] []

theorem phase2 (n : Nat) : run0 table 20 ⟨4,[false,true,true,true,true,true,true,true,true,true],(rep [true,true,true,true,true,true] (n))⟩ = some ⟨1,[true,true],([true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨1,([true]) ++ (L),([true,true,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨1,[true,true],([true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n))⟩ = some ⟨1,([true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[true,true,true,true,true,true,true,true,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true] [true,true,true,true,true,true] 6 local3 n [true] []

theorem phase4 (n : Nat) : run0 table 11 ⟨1,([true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[true,true,true,true,true,true,true,true,true,true]⟩ = some ⟨1,([false,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]) = ([false,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true]) := by
  calc
    _ = ([false,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true,true,true,true,true] [true] [true,true,true,true,true] true n
    _ = ([false,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true,true,true,true] [true,true] [true,true,true,true,true] true n
    _ = ([false,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true,true,true] [true,true,true] [true,true,true,true,true] true n
    _ = ([false,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true,true] [true,true,true,true] [true,true,true,true,true] true n
    _ = ([false,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true] [true,true,true,true,true] [true,true,true,true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (38+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 7+10*n+20+6*n+11=38+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 21 (fun n => 38+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M9002

namespace M9009

-- 1RB1LF_1RC0LB_0RD1LA_1LD1RE_1LC1RE_---1LC

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨true,false,2⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true]),[]⟩

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨4,([false]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true]),[]⟩ = some ⟨2,(rep [true,true,true] (n)) ++ ([true,true,true,true]),[true]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨2,([true,true,true]) ++ (L),(R)⟩ = some ⟨2,(L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨2,(rep [true,true,true] (n)) ++ ([true,true,true,true]),[true]⟩ = some ⟨2,[true,true,true,true],(rep [true,true,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 2 [] [] [true,true,true] [true,true,true] 3 local1 n [true,true,true,true] [true]

theorem phase2 (n : Nat) : run0 table 12 ⟨2,[true,true,true,true],(rep [true,true,true] (n)) ++ ([true])⟩ = some ⟨4,[true,true],([true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨4,([true]) ++ (L),([true,true,true,true]) ++ ([true,true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true,true]) ++ (L),([true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨4,[true,true],([true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true])⟩ = some ⟨4,([true]) ++ (rep [true,true,true] (n)) ++ ([true]),[true,true,true,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true,true,true,true] [true,true,true] [true,true,true] 3 local3 n [true] [true]

theorem phase4 (n : Nat) : run0 table 6 ⟨4,([true]) ++ (rep [true,true,true] (n)) ++ ([true]),[true,true,true,true,true]⟩ = some ⟨4,([false,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]) = ([false,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true]) := by
  calc
    _ = ([false,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true] [true] [true,true] true n
    _ = ([false,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true] [true,true] [true,true] true n
    _ = ([false,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true] [true,true,true] [true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (19+6*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 1+3*n+12+3*n+6=19+6*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (fun n => 19+6*n) entry (by intro n; omega) growth m hm

#print axioms never

end M9009

namespace M9244

-- 1RB0LB_1RC1LE_0RD1LF_1LD1RE_1LC1RE_---1LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true]),[]⟩

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 7 ⟨4,([false,true,true]) ++ ([true,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (7*n) ⟨4,([false,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true]),[]⟩ = some ⟨4,[false,true,true,true,true],(rep [true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true] [] [true,true,true] [true,true,true] 7 local0 n [true,true] []

theorem phase1 (n : Nat) : run0 table 14 ⟨4,[false,true,true,true,true],(rep [true,true,true] (n))⟩ = some ⟨4,[true],([true,true,true,true,true,true]) ++ (rep [true,true,true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 3 ⟨4,([true]) ++ (L),([true,true,true,true,true,true]) ++ ([true,true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true,true]) ++ (L),([true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (3*n) ⟨4,[true],([true,true,true,true,true,true]) ++ (rep [true,true,true] (n))⟩ = some ⟨4,([true]) ++ (rep [true,true,true] (n)),[true,true,true,true,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true,true,true,true,true,true] [true,true,true] [true,true,true] 3 local2 n [] []

theorem phase3 (n : Nat) : run0 table 7 ⟨4,([true]) ++ (rep [true,true,true] (n)),[true,true,true,true,true,true]⟩ = some ⟨4,([false,true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) = ([false,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true]) := by
  calc
    _ = ([false,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true] [] [true,true] true n
    _ = ([false,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true] [true] [true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (21+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 7*n+14+3*n+7=21+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (fun n => 21+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M9244

namespace M9534

-- 1RB0LB_1RC1LF_0RD1RB_1LD1RE_1LC1RE_---0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 9 ⟨1,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ = some ⟨1,([true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨1,([true,true,true,true]) ++ ([true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨1,([true,true,true,true]) ++ (L),([false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨1,([true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ = some ⟨1,[true,true,true,true,true],(rep [false,false,true,false,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,true,true] [] [true,true,true,true,true,true] [false,false,true,false,false,true] 6 local1 n [true] []

theorem phase2 (n : Nat) : run0 table 6 ⟨1,[true,true,true,true,true],(rep [false,false,true,false,false,true] (n))⟩ = some ⟨1,[false,true],([true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 12 ⟨1,([false]) ++ (L),([true,false,false,true]) ++ ([false,false,true,false,false,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,true,true,true,true,true]) ++ (L),([true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (12*n) ⟨1,[false,true],([true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n))⟩ = some ⟨1,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[true,false,false,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,false,false,true] [false,false,true,false,false,true] [true,true,true,true,true,true] 12 local3 n [true] []

theorem phase4 (n : Nat) : run0 table 12 ⟨1,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[true,false,false,true]⟩ = some ⟨1,([false,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]) = ([false,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (27+18*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 9+6*n+6+12*n+12=27+18*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 27+18*n) entry (by intro n; omega) growth m hm

#print axioms never

end M9534

namespace M9647

-- 1RB0LB_1RC0LE_0RD0RB_1LD1RE_1LF1RE_---0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false,true,false]) ++ (rep [true,false,true,true,true,false,true,true] (n)) ++ ([true,false,true,true]),[]⟩

theorem entry : run0 table 21 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 12 ⟨4,([false,true,false]) ++ (rep [true,false,true,true,true,false,true,true] (n)) ++ ([true,false,true,true]),[]⟩ = some ⟨4,([false,true,true,true,false,true,true]) ++ (rep [true,false,true,true,true,false,true,true] (n)) ++ ([true,false,true,true]),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 8 ⟨4,([false,true,true,true,false,true,true]) ++ ([true,false,true,true,true,false,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true,true,false,true,true]) ++ (L),([false,false,false,true,false,false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (8*n) ⟨4,([false,true,true,true,false,true,true]) ++ (rep [true,false,true,true,true,false,true,true] (n)) ++ ([true,false,true,true]),[]⟩ = some ⟨4,[false,true,true,true,false,true,true,true,false,true,true],(rep [false,false,false,true,false,false,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true,true,false,true,true] [] [true,false,true,true,true,false,true,true] [false,false,false,true,false,false,false,true] 8 local1 n [true,false,true,true] []

theorem phase2 (n : Nat) : run0 table 27 ⟨4,[false,true,true,true,false,true,true,true,false,true,true],(rep [false,false,false,true,false,false,false,true] (n))⟩ = some ⟨1,[false,true],([true,false,false,true,false,false,true,false,false,false,true]) ++ (rep [false,false,false,true,false,false,false,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 28 ⟨1,([false]) ++ (L),([true,false,false,true,false,false,true,false,false,false,true]) ++ ([false,false,false,true,false,false,false,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,true,false,true,true,true,false,true]) ++ (L),([true,false,false,true,false,false,true,false,false,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (28*n) ⟨1,[false,true],([true,false,false,true,false,false,true,false,false,false,true]) ++ (rep [false,false,false,true,false,false,false,true] (n))⟩ = some ⟨1,([false]) ++ (rep [true,true,false,true,true,true,false,true] (n)) ++ ([true]),[true,false,false,true,false,false,true,false,false,false,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,false,false,true,false,false,true,false,false,false,true] [false,false,false,true,false,false,false,true] [true,true,false,true,true,true,false,true] 28 local3 n [true] []

theorem phase4 (n : Nat) : run0 table 33 ⟨1,([false]) ++ (rep [true,true,false,true,true,true,false,true] (n)) ++ ([true]),[true,false,false,true,false,false,true,false,false,false,true]⟩ = some ⟨4,([false,true,false,true,false,true,true,true,false,true,true,true,false,true]) ++ (rep [true,true,false,true,true,true,false,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,true,false,true,true,true,false,true,true,true,false,true]) ++ (rep [true,true,false,true,true,true,false,true] (n)) ++ ([true]) = ([false,true,false,true,false,true,true,true,false,true,true]) ++ (rep [true,false,true,true,true,false,true,true] (n)) ++ ([true,false,true,true]) := by
  calc
    _ = ([false,true,false,true,false,true,true,true,false,true,true,true,false]) ++ (rep [true,true,true,false,true,true,true,false] (n)) ++ ([true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,false,true,false,true,true,true,false,true,true,true,false] [true] [true,true,false,true,true,true,false] true n
    _ = ([false,true,false,true,false,true,true,true,false,true,true,true]) ++ (rep [false,true,true,true,false,true,true,true] (n)) ++ ([false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,false,true,false,true,true,true,false,true,true,true] [true,true] [true,true,true,false,true,true,true] false n
    _ = ([false,true,false,true,false,true,true,true,false,true,true]) ++ (rep [true,false,true,true,true,false,true,true] (n)) ++ ([true,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,false,true,false,true,true,true,false,true,true] [false,true,true] [false,true,true,true,false,true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (72+36*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 12+8*n+27+28*n+33=72+36*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 21 (fun n => 72+36*n) entry (by intro n; omega) growth m hm

#print axioms never

end M9647

namespace M9649

-- 1RB0LB_1RC0LE_0RD1RB_1LD1RE_1LF1RE_---0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨1,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ = some ⟨4,([false,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 10 ⟨4,([false,true,true,true]) ++ ([true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true,true]) ++ (L),([false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (10*n) ⟨4,([false,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ = some ⟨4,[false,true,true,true,true],(rep [false,false,true,false,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true,true] [] [true,true,true,true,true,true] [false,false,true,false,false,true] 10 local1 n [true] []

theorem phase2 (n : Nat) : run0 table 8 ⟨4,[false,true,true,true,true],(rep [false,false,true,false,false,true] (n))⟩ = some ⟨1,[false,true],([true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 10 ⟨1,([false]) ++ (L),([true,false,false,true]) ++ ([false,false,true,false,false,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,true,true,true,true,true]) ++ (L),([true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (10*n) ⟨1,[false,true],([true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n))⟩ = some ⟨1,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[true,false,false,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,false,false,true] [false,false,true,false,false,true] [true,true,true,true,true,true] 10 local3 n [true] []

theorem phase4 (n : Nat) : run0 table 10 ⟨1,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[true,false,false,true]⟩ = some ⟨1,([false,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]) = ([false,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (25+20*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 7+10*n+8+10*n+10=25+20*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 25+20*n) entry (by intro n; omega) growth m hm

#print axioms never

end M9649

namespace M9664

-- 1RB0LB_1RC1LF_0RD1RB_1LD1RE_1LF1RE_---0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 8 ⟨1,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ = some ⟨5,([true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[true]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨5,([true,true,true]) ++ ([true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨5,([true,true,true]) ++ (L),([true,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨5,([true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[true]⟩ = some ⟨5,[true,true,true,true],(rep [true,false,false,true,false,false] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,true,true] [] [true,true,true,true,true,true] [true,false,false,true,false,false] 6 local1 n [true] [true]

theorem phase2 (n : Nat) : run0 table 5 ⟨5,[true,true,true,true],(rep [true,false,false,true,false,false] (n)) ++ ([true])⟩ = some ⟨1,[false,true],([true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 10 ⟨1,([false]) ++ (L),([true,false,false]) ++ ([true,false,false,true,false,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,true,true,true,true,true]) ++ (L),([true,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (10*n) ⟨1,[false,true],([true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true])⟩ = some ⟨1,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[true,false,false,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,false,false] [true,false,false,true,false,false] [true,true,true,true,true,true] 10 local3 n [true] [true]

theorem phase4 (n : Nat) : run0 table 10 ⟨1,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[true,false,false,true]⟩ = some ⟨1,([false,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]) = ([false,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (23+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 8+6*n+5+10*n+10=23+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 23+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M9664

namespace M10505

-- 1RB---_1RC1RD_0RD0RA_1LD1RE_1LF1RE_1LB0LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false,true,true,true,true]) ++ (rep [true,false,true] (n)),[]⟩

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 3 ⟨4,([false,true,true,true,true]) ++ (rep [true,false,true] (n)),[]⟩ = some ⟨5,([true,true]) ++ (rep [true,false,true] (n)),[false,false,true]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 7 ⟨5,([true,true]) ++ ([true,false,true]) ++ (L),(R)⟩ = some ⟨5,([true,true]) ++ (L),([true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (7*n) ⟨5,([true,true]) ++ (rep [true,false,true] (n)),[false,false,true]⟩ = some ⟨5,[true,true],(rep [true,false,false] (n)) ++ ([false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,true] [] [true,false,true] [true,false,false] 7 local1 n [] [false,false,true]

theorem phase2 (n : Nat) : run0 table 4 ⟨5,[true,true],(rep [true,false,false] (n)) ++ ([false,false,true])⟩ = some ⟨2,[true,true],([false,false]) ++ (rep [true,false,false] (n)) ++ ([false,false,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨2,([true]) ++ (L),([false,false]) ++ ([true,false,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true,false]) ++ (L),([false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨2,[true,true],([false,false]) ++ (rep [true,false,false] (n)) ++ ([false,false,true])⟩ = some ⟨2,([true]) ++ (rep [true,true,false] (n)) ++ ([true]),[false,false,false,false,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,false] [true,false,false] [true,true,false] 3 local3 n [true] [false,false,true]

theorem phase4 (n : Nat) : run0 table 10 ⟨2,([true]) ++ (rep [true,true,false] (n)) ++ ([true]),[false,false,false,false,true]⟩ = some ⟨4,([false,true,true,true,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true]) = ([false,true,true,true,true,true,false,true]) ++ (rep [true,false,true] (n)) := by
  calc
    _ = ([false,true,true,true,true,true,false,true]) ++ (rep [true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,false] [] [true,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (17+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 3+7*n+4+3*n+10=17+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (fun n => 17+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M10505

namespace M10506

-- 1RB---_1RC1RE_0RD0RA_1LD1RE_1LF1RE_1LB0LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false,true,true,true,true]) ++ (rep [true,false,true] (n)),[]⟩

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 3 ⟨4,([false,true,true,true,true]) ++ (rep [true,false,true] (n)),[]⟩ = some ⟨5,([true,true]) ++ (rep [true,false,true] (n)),[false,false,true]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 7 ⟨5,([true,true]) ++ ([true,false,true]) ++ (L),(R)⟩ = some ⟨5,([true,true]) ++ (L),([true,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (7*n) ⟨5,([true,true]) ++ (rep [true,false,true] (n)),[false,false,true]⟩ = some ⟨5,[true,true],(rep [true,false,false] (n)) ++ ([false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,true] [] [true,false,true] [true,false,false] 7 local1 n [] [false,false,true]

theorem phase2 (n : Nat) : run0 table 4 ⟨5,[true,true],(rep [true,false,false] (n)) ++ ([false,false,true])⟩ = some ⟨2,[true,true],([false,false]) ++ (rep [true,false,false] (n)) ++ ([false,false,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨2,([true]) ++ (L),([false,false]) ++ ([true,false,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true,false]) ++ (L),([false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨2,[true,true],([false,false]) ++ (rep [true,false,false] (n)) ++ ([false,false,true])⟩ = some ⟨2,([true]) ++ (rep [true,true,false] (n)) ++ ([true]),[false,false,false,false,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,false] [true,false,false] [true,true,false] 3 local3 n [true] [false,false,true]

theorem phase4 (n : Nat) : run0 table 10 ⟨2,([true]) ++ (rep [true,true,false] (n)) ++ ([true]),[false,false,false,false,true]⟩ = some ⟨4,([false,true,true,true,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true]) = ([false,true,true,true,true,true,false,true]) ++ (rep [true,false,true] (n)) := by
  calc
    _ = ([false,true,true,true,true,true,false,true]) ++ (rep [true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,false] [] [true,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (17+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 3+7*n+4+3*n+10=17+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (fun n => 17+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M10506

namespace M10524

-- 1RB0LE_1RC1RF_0RD---_1LD1RE_1LF1RE_1LA0RA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,true,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false,true,true,true,true]) ++ (rep [false,true,true] (n)),[]⟩

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 9 ⟨4,([false,true,true,true,true]) ++ (rep [false,true,true] (n)),[]⟩ = some ⟨4,([false,true]) ++ (rep [false,true,true] (n)),[false,false,false]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 7 ⟨4,([false,true]) ++ ([false,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true]) ++ (L),([true,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (7*n) ⟨4,([false,true]) ++ (rep [false,true,true] (n)),[false,false,false]⟩ = some ⟨4,[false,true],(rep [true,true,false] (n)) ++ ([false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true] [] [false,true,true] [true,true,false] 7 local1 n [] [false,false,false]

theorem phase2 (n : Nat) : run0 table 6 ⟨4,[false,true],(rep [true,true,false] (n)) ++ ([false,false,false])⟩ = some ⟨1,[true,true],([true,false]) ++ (rep [true,true,false] (n)) ++ ([false,false,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([true]) ++ (L),([true,false]) ++ ([true,true,false]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨1,[true,true],([true,false]) ++ (rep [true,true,false] (n)) ++ ([false,false,false])⟩ = some ⟨1,([true]) ++ (rep [true,false,true] (n)) ++ ([true]),[true,false,false,false,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,false] [true,true,false] [true,false,true] 3 local3 n [true] [false,false,false]

theorem phase4 (n : Nat) : run0 table 10 ⟨1,([true]) ++ (rep [true,false,true] (n)) ++ ([true]),[true,false,false,false,false]⟩ = some ⟨4,([false,true,true,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true]) = ([false,true,true,true,true,false,true,true]) ++ (rep [false,true,true] (n)) := by
  calc
    _ = ([false,true,true,true,true,false,true,true]) ++ (rep [false,true,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,false,true] [] [false,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (25+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 9+7*n+6+3*n+10=25+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (fun n => 25+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M10524

namespace M11011

-- 1RB1LC_1RC0LB_0RD0LE_1LD1RE_1LF1RE_---1LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true]),[]⟩

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 5 ⟨4,([false,true]) ++ ([true,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (5*n) ⟨4,([false,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true]),[]⟩ = some ⟨4,[false,true,true,true,true],(rep [true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true] [] [true,true,true] [true,true,true] 5 local0 n [true,true,true] []

theorem phase1 (n : Nat) : run0 table 15 ⟨4,[false,true,true,true,true],(rep [true,true,true] (n))⟩ = some ⟨4,[true,true],([true,true,true,true,true]) ++ (rep [true,true,true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 3 ⟨4,([true]) ++ (L),([true,true,true,true,true]) ++ ([true,true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true,true]) ++ (L),([true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (3*n) ⟨4,[true,true],([true,true,true,true,true]) ++ (rep [true,true,true] (n))⟩ = some ⟨4,([true]) ++ (rep [true,true,true] (n)) ++ ([true]),[true,true,true,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true,true,true,true,true] [true,true,true] [true,true,true] 3 local2 n [true] []

theorem phase3 (n : Nat) : run0 table 6 ⟨4,([true]) ++ (rep [true,true,true] (n)) ++ ([true]),[true,true,true,true,true]⟩ = some ⟨4,([false,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]) = ([false,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true]) := by
  calc
    _ = ([false,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true] [true] [true,true] true n
    _ = ([false,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true] [true,true] [true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (21+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 5*n+15+3*n+6=21+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (fun n => 21+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M11011

namespace M11028

-- 1RB1LC_1RC0LB_0RD1LF_1LD1RE_1LF1RE_---1LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true]),[]⟩

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨4,([false]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true]),[]⟩ = some ⟨5,(rep [true,true,true] (n)) ++ ([true,true,true,true]),[true]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨5,([true,true,true]) ++ (L),(R)⟩ = some ⟨5,(L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨5,(rep [true,true,true] (n)) ++ ([true,true,true,true]),[true]⟩ = some ⟨5,[true,true,true,true],(rep [true,true,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [] [] [true,true,true] [true,true,true] 3 local1 n [true,true,true,true] [true]

theorem phase2 (n : Nat) : run0 table 12 ⟨5,[true,true,true,true],(rep [true,true,true] (n)) ++ ([true])⟩ = some ⟨4,[true,true],([true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨4,([true]) ++ (L),([true,true,true,true]) ++ ([true,true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true,true]) ++ (L),([true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨4,[true,true],([true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true])⟩ = some ⟨4,([true]) ++ (rep [true,true,true] (n)) ++ ([true]),[true,true,true,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true,true,true,true] [true,true,true] [true,true,true] 3 local3 n [true] [true]

theorem phase4 (n : Nat) : run0 table 6 ⟨4,([true]) ++ (rep [true,true,true] (n)) ++ ([true]),[true,true,true,true,true]⟩ = some ⟨4,([false,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]) = ([false,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true]) := by
  calc
    _ = ([false,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true] [true] [true,true] true n
    _ = ([false,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true] [true,true] [true,true] true n
    _ = ([false,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true] [true,true,true] [true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (19+6*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 1+3*n+12+3*n+6=19+6*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (fun n => 19+6*n) entry (by intro n; omega) growth m hm

#print axioms never

end M11028

namespace M11155

-- 1RB1LE_1RC0LA_0RD0RD_1LD1RE_1LF1RE_---1LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false,true,true]) ++ (rep [true,true] (n)) ++ ([true,false,true,true,true,true]),[]⟩

theorem entry : run0 table 44 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 6 ⟨4,([false,true,true]) ++ ([true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (6*n) ⟨4,([false,true,true]) ++ (rep [true,true] (n)) ++ ([true,false,true,true,true,true]),[]⟩ = some ⟨4,[false,true,true,true,false,true,true,true,true],(rep [true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true] [] [true,true] [true,true] 6 local0 n [true,false,true,true,true,true] []

theorem phase1 (n : Nat) : run0 table 33 ⟨4,[false,true,true,true,false,true,true,true,true],(rep [true,true] (n))⟩ = some ⟨4,[true,true,false,true,true,true,true],([true,true,true]) ++ (rep [true,true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 2 ⟨4,([true]) ++ (L),([true,true,true]) ++ ([true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (2*n) ⟨4,[true,true,false,true,true,true,true],([true,true,true]) ++ (rep [true,true] (n))⟩ = some ⟨4,([true]) ++ (rep [true,true] (n)) ++ ([true,false,true,true,true,true]),[true,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true,true,true] [true,true] [true,true] 2 local2 n [true,false,true,true,true,true] []

theorem phase3 (n : Nat) : run0 table 4 ⟨4,([true]) ++ (rep [true,true] (n)) ++ ([true,false,true,true,true,true]),[true,true,true]⟩ = some ⟨4,([false,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,false,true,true,true,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,false,true,true,true,true]) = ([false,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,false,true,true,true,true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (37+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [show 6*n+33+2*n+4=37+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 44 (fun n => 37+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M11155

namespace M11156

-- 1RB1LE_1RC0LA_0RD0RE_1LD1RE_1LF1RE_---1LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false,true,true]) ++ (rep [true,true] (n)) ++ ([true,false,true,true,true,true]),[]⟩

theorem entry : run0 table 44 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 6 ⟨4,([false,true,true]) ++ ([true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (6*n) ⟨4,([false,true,true]) ++ (rep [true,true] (n)) ++ ([true,false,true,true,true,true]),[]⟩ = some ⟨4,[false,true,true,true,false,true,true,true,true],(rep [true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true] [] [true,true] [true,true] 6 local0 n [true,false,true,true,true,true] []

theorem phase1 (n : Nat) : run0 table 32 ⟨4,[false,true,true,true,false,true,true,true,true],(rep [true,true] (n))⟩ = some ⟨4,[true,false,true,true,true,true],([true,true,true,true]) ++ (rep [true,true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 2 ⟨4,([true]) ++ (L),([true,true,true,true]) ++ ([true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true]) ++ (L),([true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (2*n) ⟨4,[true,false,true,true,true,true],([true,true,true,true]) ++ (rep [true,true] (n))⟩ = some ⟨4,([true]) ++ (rep [true,true] (n)) ++ ([false,true,true,true,true]),[true,true,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true,true,true,true] [true,true] [true,true] 2 local2 n [false,true,true,true,true] []

theorem phase3 (n : Nat) : run0 table 5 ⟨4,([true]) ++ (rep [true,true] (n)) ++ ([false,true,true,true,true]),[true,true,true,true]⟩ = some ⟨4,([false,true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false,true,true,true,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false,true,true,true,true]) = ([false,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,false,true,true,true,true]) := by
  calc
    _ = ([false,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,false,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true] [false,true,true,true,true] [true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (37+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n))
  rw [finalL n] at H
  rw [show 6*n+32+2*n+5=37+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 44 (fun n => 37+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M11156

namespace M11231

-- 1RB---_1RC0LF_0RD1RC_1LD1RE_1LF1RE_0LA1LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true,true,true,true]),[]⟩

theorem entry : run0 table 25 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨2,([false,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true,true,true,true]),[]⟩ = some ⟨5,([true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true,true,true,true]),[true]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨5,([true,true,true]) ++ ([true,true,true,true]) ++ (L),(R)⟩ = some ⟨5,([true,true,true]) ++ (L),([false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨5,([true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true,true,true,true]),[true]⟩ = some ⟨5,[true,true,true,true,true,true,true,true,true],(rep [false,true,false,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,true,true] [] [true,true,true,true] [false,true,false,true] 4 local1 n [true,true,true,true,true,true] [true]

theorem phase2 (n : Nat) : run0 table 10 ⟨5,[true,true,true,true,true,true,true,true,true],(rep [false,true,false,true] (n)) ++ ([true])⟩ = some ⟨2,[true,true],([false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 8 ⟨2,([true]) ++ (L),([false,true,false,true,false,true,false,true]) ++ ([false,true,false,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true,true,true]) ++ (L),([false,true,false,true,false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (8*n) ⟨2,[true,true],([false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true])⟩ = some ⟨2,([true]) ++ (rep [true,true,true,true] (n)) ++ ([true]),[false,true,false,true,false,true,false,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,true,false,true,false,true,false,true] [false,true,false,true] [true,true,true,true] 8 local3 n [true] [true]

theorem phase4 (n : Nat) : run0 table 18 ⟨2,([true]) ++ (rep [true,true,true,true] (n)) ++ ([true]),[false,true,false,true,false,true,false,true,true]⟩ = some ⟨2,([false,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true]) = ([false,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true,true,true,true]) := by
  calc
    _ = ([false,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true,true,true,true] [true] [true,true,true] true n
    _ = ([false,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true,true,true] [true,true] [true,true,true] true n
    _ = ([false,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true,true] [true,true,true] [true,true,true] true n
    _ = ([false,true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true] [true,true,true,true] [true,true,true] true n
    _ = ([false,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([true,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true] [true,true,true,true,true] [true,true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (35+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 7+4*n+10+8*n+18=35+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 25 (fun n => 35+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M11231

namespace M11265

-- 1RB---_1RC0LF_0RD1RB_1LD1RE_1LF1RE_1LA1LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) ++ ([false,true,false,true,false,true,true])⟩

theorem entry : run0 table 32 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨1,[],([true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) ++ ([false,true,false,true,false,true,true])⟩ = some ⟨2,[true,true],(rep [false,true,false,true,false,true,false,true] (n)) ++ ([false,true,false,true,false,true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 8 ⟨2,([true]) ++ (L),([false,true,false,true,false,true,false,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true,true,true,true,true,true,true]) ++ (L),(R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (8*n) ⟨2,[true,true],(rep [false,true,false,true,false,true,false,true] (n)) ++ ([false,true,false,true,false,true,true])⟩ = some ⟨2,([true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true]),[false,true,false,true,false,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [] [false,true,false,true,false,true,false,true] [true,true,true,true,true,true,true,true] 8 local1 n [true] [false,true,false,true,false,true,true]

theorem phase2 (n : Nat) : run0 table 7 ⟨2,([true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true]),[false,true,false,true,false,true,true]⟩ = some ⟨1,([true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 8 ⟨1,([true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨1,([true,true,true,true,true,true,true,true]) ++ (L),([true,false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (8*n) ⟨1,([true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ = some ⟨1,[true,true,true,true,true,true,true,true,true],(rep [true,false,true,false,true,false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true] [true,false,true,false,true,false,true,false] 8 local3 n [true] []

theorem phase4 (n : Nat) : run0 table 29 ⟨1,[true,true,true,true,true,true,true,true,true],(rep [true,false,true,false,true,false,true,false] (n))⟩ = some ⟨2,[true,true],([false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n))⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 8 ⟨2,([true]) ++ (L),([false,true,false,true,false,true,false,true,false,true,false]) ++ ([true,false,true,false,true,false,true,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true,true,true,true,true,true,true]) ++ (L),([false,true,false,true,false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (8*n) ⟨2,[true,true],([false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n))⟩ = some ⟨2,([true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true]),[false,true,false,true,false,true,false,true,false,true,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,true,false,true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false] [true,true,true,true,true,true,true,true] 8 local5 n [true] []

theorem phase6 (n : Nat) : run0 table 19 ⟨2,([true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true]),[false,true,false,true,false,true,false,true,false,true,false]⟩ = some ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true]),[true]⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 8 ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),([false,true,false,true,false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (8*n) ⟨5,([true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true]),[true]⟩ = some ⟨5,[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true],(rep [false,true,false,true,false,true,false,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true] [false,true,false,true,false,true,false,true] 8 local7 n [true] [true]

theorem phase8 (n : Nat) : run0 table 15 ⟨5,[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true],(rep [false,true,false,true,false,true,false,true] (n)) ++ ([true])⟩ = some ⟨1,[],([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) ++ ([true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) ++ ([true]) = ([true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) ++ ([false,true,false,true,false,true,true]) := by
  calc
    _ = ([true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,false,true,false,true,false,true,false,true,false,true,false,true,false] [true] [false,true,false,true,false,true,false] true n
    _ = ([true,false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) ++ ([false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,false,true,false,true,false,true,false,true,false,true,false,true] [true,true] [true,false,true,false,true,false,true] false n
    _ = ([true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,false,true,false,true,false,true,false,true,false,true,false] [false,true,true] [false,true,false,true,false,true,false] true n
    _ = ([true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) ++ ([false,true,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,false,true,false,true,false,true,false,true,false,true] [true,false,true,true] [true,false,true,false,true,false,true] false n
    _ = ([true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false] (n)) ++ ([true,false,true,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,false,true,false,true,false,true,false,true,false] [false,true,false,true,true] [false,true,false,true,false,true,false] true n
    _ = ([true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true] (n)) ++ ([false,true,false,true,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,false,true,false,true,false,true,false,true] [true,false,true,false,true,true] [true,false,true,false,true,false,true] false n

theorem growth (n : Nat) : run0 table (71+32*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalR n] at H
  rw [show 1+8*n+7+8*n+29+8*n+19+8*n+15=71+32*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 32 (fun n => 71+32*n) entry (by intro n; omega) growth m hm

#print axioms never

end M11265

namespace M11633

-- 1RB0LE_1RC0LB_0RD1LA_1LD1RE_1LF1RE_---1LC

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨true,false,2⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([false,false]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,true])⟩

theorem entry : run0 table 32 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 5 ⟨1,[],([false,false]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,true])⟩ = some ⟨4,[true,true],([true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨4,([true]) ++ (L),([true]) ++ ([true,true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨4,[true,true],([true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,true])⟩ = some ⟨4,([true]) ++ (rep [true,true,true] (n)) ++ ([true]),[true,true,true,true,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true] [true,true,true] [true,true,true] 3 local1 n [true] [true,true,true,true,true]

theorem phase2 (n : Nat) : run0 table 7 ⟨4,([true]) ++ (rep [true,true,true] (n)) ++ ([true]),[true,true,true,true,true,true]⟩ = some ⟨4,([false,true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 5 ⟨4,([false,true,true,true,true,true,true,true]) ++ ([true,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true,true,true,true,true,true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (5*n) ⟨4,([false,true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]),[]⟩ = some ⟨4,[false,true,true,true,true,true,true,true,true],(rep [true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true,true,true,true,true,true] [] [true,true,true] [true,true,true] 5 local3 n [true] []

theorem phase4 (n : Nat) : run0 table 16 ⟨4,[false,true,true,true,true,true,true,true,true],(rep [true,true,true] (n))⟩ = some ⟨1,[],([false,false,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) = ([false,false,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,true]) := by
  calc
    _ = ([false,false,true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,false,true,true,true,true,true,true,true] [] [true,true] true n
    _ = ([false,false,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,false,true,true,true,true,true,true] [true] [true,true] true n
    _ = ([false,false,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,false,true,true,true,true,true] [true,true] [true,true] true n
    _ = ([false,false,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,false,true,true,true,true] [true,true,true] [true,true] true n
    _ = ([false,false,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,false,true,true,true] [true,true,true,true] [true,true] true n

theorem growth (n : Nat) : run0 table (28+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 5+3*n+7+5*n+16=28+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 32 (fun n => 28+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M11633

namespace M11678

-- 1RB1LF_1RC0LB_0RD1LA_1LD1RE_1LF1RE_---1LC

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨true,false,2⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([false,false]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,true])⟩

theorem entry : run0 table 28 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 5 ⟨1,[],([false,false]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,true])⟩ = some ⟨4,[true,true],([true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨4,([true]) ++ (L),([true]) ++ ([true,true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨4,[true,true],([true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,true])⟩ = some ⟨4,([true]) ++ (rep [true,true,true] (n)) ++ ([true]),[true,true,true,true,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true] [true,true,true] [true,true,true] 3 local1 n [true] [true,true,true,true,true]

theorem phase2 (n : Nat) : run0 table 8 ⟨4,([true]) ++ (rep [true,true,true] (n)) ++ ([true]),[true,true,true,true,true,true]⟩ = some ⟨5,([true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]),[true]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨5,([true,true,true,true,true,true,true]) ++ ([true,true,true]) ++ (L),(R)⟩ = some ⟨5,([true,true,true,true,true,true,true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨5,([true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]),[true]⟩ = some ⟨5,[true,true,true,true,true,true,true,true],(rep [true,true,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,true,true,true,true,true,true] [] [true,true,true] [true,true,true] 3 local3 n [true] [true]

theorem phase4 (n : Nat) : run0 table 11 ⟨5,[true,true,true,true,true,true,true,true],(rep [true,true,true] (n)) ++ ([true])⟩ = some ⟨1,[],([false,false,true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]) = ([false,false,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,true]) := by
  calc
    _ = ([false,false,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,false,true,true,true,true,true,true] [true] [true,true] true n
    _ = ([false,false,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,false,true,true,true,true,true] [true,true] [true,true] true n
    _ = ([false,false,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,false,true,true,true,true] [true,true,true] [true,true] true n
    _ = ([false,false,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,false,true,true,true] [true,true,true,true] [true,true] true n

theorem growth (n : Nat) : run0 table (24+6*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 5+3*n+8+3*n+11=24+6*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 28 (fun n => 24+6*n) entry (by intro n; omega) growth m hm

#print axioms never

end M11678

namespace M13016

-- 1RB1LA_1RC0RC_0RD0LF_1LD1RE_1RF1RE_0LA---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,([false]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,true]),[]⟩

theorem entry : run0 table 9 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨5,([false]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,true]),[]⟩ = some ⟨0,(rep [true,true,true] (n)) ++ ([true,true,true,true,true]),[false]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨0,([true,true,true]) ++ (L),(R)⟩ = some ⟨0,(L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨0,(rep [true,true,true] (n)) ++ ([true,true,true,true,true]),[false]⟩ = some ⟨0,[true,true,true,true,true],(rep [true,true,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [] [] [true,true,true] [true,true,true] 3 local1 n [true,true,true,true,true] [false]

theorem phase2 (n : Nat) : run0 table 17 ⟨0,[true,true,true,true,true],(rep [true,true,true] (n)) ++ ([false])⟩ = some ⟨4,[true,true],([true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨4,([true]) ++ (L),([true,true,true,true,true]) ++ ([true,true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true,true]) ++ (L),([true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨4,[true,true],([true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false])⟩ = some ⟨4,([true]) ++ (rep [true,true,true] (n)) ++ ([true]),[true,true,true,true,true,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true,true,true,true,true] [true,true,true] [true,true,true] 3 local3 n [true] [false]

theorem phase4 (n : Nat) : run0 table 7 ⟨4,([true]) ++ (rep [true,true,true] (n)) ++ ([true]),[true,true,true,true,true,false]⟩ = some ⟨5,([false,true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]) = ([false,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,true]) := by
  calc
    _ = ([false,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true] [true] [true,true] true n
    _ = ([false,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true] [true,true] [true,true] true n
    _ = ([false,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true] [true,true,true] [true,true] true n
    _ = ([false,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true] [true,true,true,true] [true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (25+6*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 1+3*n+17+3*n+7=25+6*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 9 (fun n => 25+6*n) entry (by intro n; omega) growth m hm

#print axioms never

end M13016

namespace M13206

-- 1RB0LA_1RC1LB_0RD1LA_1LD1RE_1RF1RE_0LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true]),[]⟩

theorem entry : run0 table 9 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨5,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true]),[]⟩ = some ⟨1,(rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true]),[false]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨1,([true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨1,(L),([true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨1,(rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true]),[false]⟩ = some ⟨1,[true,true,true,true,true],(rep [true,true,true,true,true,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [] [] [true,true,true,true,true,true] [true,true,true,true,true,true] 6 local1 n [true,true,true,true,true] [false]

theorem phase2 (n : Nat) : run0 table 17 ⟨1,[true,true,true,true,true],(rep [true,true,true,true,true,true] (n)) ++ ([false])⟩ = some ⟨4,[true,true,false,true,true],([true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨4,([true]) ++ (L),([true,true,true]) ++ ([true,true,true,true,true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true,true,true,true,true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨4,[true,true,false,true,true],([true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false])⟩ = some ⟨4,([true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,false,true,true]),[true,true,true,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true,true,true] [true,true,true,true,true,true] [true,true,true,true,true,true] 6 local3 n [true,false,true,true] [false]

theorem phase4 (n : Nat) : run0 table 6 ⟨4,([true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,false,true,true]),[true,true,true,false]⟩ = some ⟨1,([true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,false,true,true]),[false]⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 6 ⟨1,([true,true,true,true,true]) ++ ([true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨1,([true,true,true,true,true]) ++ (L),([true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (6*n) ⟨1,([true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,false,true,true]),[false]⟩ = some ⟨1,[true,true,true,true,true,true,false,true,true],(rep [true,true,true,true,true,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,true,true,true] [] [true,true,true,true,true,true] [true,true,true,true,true,true] 6 local5 n [true,false,true,true] [false]

theorem phase6 (n : Nat) : run0 table 17 ⟨1,[true,true,true,true,true,true,false,true,true],(rep [true,true,true,true,true,true] (n)) ++ ([false])⟩ = some ⟨4,[true,true,true],([true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 6 ⟨4,([true]) ++ (L),([true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (6*n) ⟨4,[true,true,true],([true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false])⟩ = some ⟨4,([true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true]),[true,true,true,true,true,true,true,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true,true,true,true,true,true,true] [true,true,true,true,true,true] [true,true,true,true,true,true] 6 local7 n [true,true] [false]

theorem phase8 (n : Nat) : run0 table 9 ⟨4,([true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true]),[true,true,true,true,true,true,true,false]⟩ = some ⟨5,([false,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true]) = ([false,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true]) := by
  calc
    _ = ([false,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true,true,true] [true,true] [true,true,true,true,true] true n
    _ = ([false,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true,true] [true,true,true] [true,true,true,true,true] true n
    _ = ([false,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true] [true,true,true,true] [true,true,true,true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (50+24*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalL n] at H
  rw [show 1+6*n+17+6*n+6+6*n+17+6*n+9=50+24*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 9 (fun n => 50+24*n) entry (by intro n; omega) growth m hm

#print axioms never

end M13206

namespace M13226

-- 1RB0LA_1RC1LB_0RD1RA_1LD1RE_1RF1RE_0LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,([false]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,true]),[]⟩

theorem entry : run0 table 9 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨5,([false]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,true]),[]⟩ = some ⟨1,(rep [true,true,true] (n)) ++ ([true,true,true,true,true]),[false]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨1,([true,true,true]) ++ (L),(R)⟩ = some ⟨1,(L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨1,(rep [true,true,true] (n)) ++ ([true,true,true,true,true]),[false]⟩ = some ⟨1,[true,true,true,true,true],(rep [true,true,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [] [] [true,true,true] [true,true,true] 3 local1 n [true,true,true,true,true] [false]

theorem phase2 (n : Nat) : run0 table 16 ⟨1,[true,true,true,true,true],(rep [true,true,true] (n)) ++ ([false])⟩ = some ⟨4,[true,true,true],([true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨4,([true]) ++ (L),([true,true,true,true]) ++ ([true,true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true,true]) ++ (L),([true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨4,[true,true,true],([true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false])⟩ = some ⟨4,([true]) ++ (rep [true,true,true] (n)) ++ ([true,true]),[true,true,true,true,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true,true,true,true] [true,true,true] [true,true,true] 3 local3 n [true,true] [false]

theorem phase4 (n : Nat) : run0 table 6 ⟨4,([true]) ++ (rep [true,true,true] (n)) ++ ([true,true]),[true,true,true,true,false]⟩ = some ⟨5,([false,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true]) = ([false,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,true]) := by
  calc
    _ = ([false,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true] [true,true] [true,true] true n
    _ = ([false,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true] [true,true,true] [true,true] true n
    _ = ([false,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true] [true,true,true,true] [true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (23+6*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 1+3*n+16+3*n+6=23+6*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 9 (fun n => 23+6*n) entry (by intro n; omega) growth m hm

#print axioms never

end M13226

namespace M13442

-- 1RB0LF_1RC0RA_0RD---_1LD1RE_1RF1RE_1LA0LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],(rep [false,true,false,true] (n)) ++ ([false,false,false,false,false,true])⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨5,[],(rep [false,true,false,true] (n)) ++ ([false,false,false,false,false,true])⟩ = some ⟨1,[true,true],(rep [false,true,false,true] (n)) ++ ([false,false,false,false,false,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨1,([true]) ++ (L),([false,true,false,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true,false]) ++ (L),(R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨1,[true,true],(rep [false,true,false,true] (n)) ++ ([false,false,false,false,false,true])⟩ = some ⟨1,([true]) ++ (rep [true,false,true,false] (n)) ++ ([true]),[false,false,false,false,false,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [] [false,true,false,true] [true,false,true,false] 4 local1 n [true] [false,false,false,false,false,true]

theorem phase2 (n : Nat) : run0 table 16 ⟨1,([true]) ++ (rep [true,false,true,false] (n)) ++ ([true]),[false,false,false,false,false,true]⟩ = some ⟨5,([false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),[false,false,false,false,false,false]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 4 ⟨5,([false]) ++ ([true,false,true,false]) ++ (L),(R)⟩ = some ⟨5,([false]) ++ (L),([false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (4*n) ⟨5,([false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),[false,false,false,false,false,false]⟩ = some ⟨5,[false,true],(rep [false,true,false,true] (n)) ++ ([false,false,false,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false] [] [true,false,true,false] [false,true,false,true] 4 local3 n [true] [false,false,false,false,false,false]

theorem phase4 (n : Nat) : run0 table 4 ⟨5,[false,true],(rep [false,true,false,true] (n)) ++ ([false,false,false,false,false,false])⟩ = some ⟨1,[true,true],([false,true]) ++ (rep [false,true,false,true] (n)) ++ ([false,false,false,false,false,false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 4 ⟨1,([true]) ++ (L),([false,true]) ++ ([false,true,false,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true,false]) ++ (L),([false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (4*n) ⟨1,[true,true],([false,true]) ++ (rep [false,true,false,true] (n)) ++ ([false,false,false,false,false,false])⟩ = some ⟨1,([true]) ++ (rep [true,false,true,false] (n)) ++ ([true]),[false,true,false,false,false,false,false,false]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,true] [false,true,false,true] [true,false,true,false] 4 local5 n [true] [false,false,false,false,false,false]

theorem phase6 (n : Nat) : run0 table 18 ⟨1,([true]) ++ (rep [true,false,true,false] (n)) ++ ([true]),[false,true,false,false,false,false,false,false]⟩ = some ⟨5,([false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),[false,false,false,false,false,true]⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 4 ⟨5,([false,true,false]) ++ ([true,false,true,false]) ++ (L),(R)⟩ = some ⟨5,([false,true,false]) ++ (L),([false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (4*n) ⟨5,([false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),[false,false,false,false,false,true]⟩ = some ⟨5,[false,true,false,true],(rep [false,true,false,true] (n)) ++ ([false,false,false,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true,false] [] [true,false,true,false] [false,true,false,true] 4 local7 n [true] [false,false,false,false,false,true]

theorem phase8 (n : Nat) : run0 table 4 ⟨5,[false,true,false,true],(rep [false,true,false,true] (n)) ++ ([false,false,false,false,false,true])⟩ = some ⟨5,[],([false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([false,false,false,false,false,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([false,false,false,false,false,true]) = ([false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([false,false,false,false,false,true]) := by
  rfl

theorem growth (n : Nat) : run0 table (44+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 2+4*n+16+4*n+4+4*n+18+4*n+4=44+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 15 (fun n => 44+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M13442

namespace M13846

-- 1RB0LB_1RC1LA_0RD---_1LD1RE_1RF1RE_1LB1RC

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,true,2⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,[],([true]) ++ (rep [false,true,false,true] (n)) ++ ([false,true,false,true,true])⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 4 ⟨0,[],([true]) ++ (rep [false,true,false,true] (n)) ++ ([false,true,false,true,true])⟩ = some ⟨2,[false,true],([true]) ++ (rep [false,true,false,true] (n)) ++ ([false,true,false,true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨2,([false]) ++ (L),([true]) ++ ([false,true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,true,false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨2,[false,true],([true]) ++ (rep [false,true,false,true] (n)) ++ ([false,true,false,true,true])⟩ = some ⟨2,([false]) ++ (rep [true,true,true,false] (n)) ++ ([true]),[true,false,true,false,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true] [false,true,false,true] [true,true,true,false] 4 local1 n [true] [false,true,false,true,true]

theorem phase2 (n : Nat) : run0 table 9 ⟨2,([false]) ++ (rep [true,true,true,false] (n)) ++ ([true]),[true,false,true,false,true,true]⟩ = some ⟨1,([true,true,true,false,true,true,true,false]) ++ (rep [true,true,true,false] (n)) ++ ([true]),[true]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨1,([true,true,true,false,true,true,true,false]) ++ ([true,true,true,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,true,false,true,true,true,false]) ++ (L),([false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨1,([true,true,true,false,true,true,true,false]) ++ (rep [true,true,true,false] (n)) ++ ([true]),[true]⟩ = some ⟨1,[true,true,true,false,true,true,true,false,true],(rep [false,true,false,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,true,false,true,true,true,false] [] [true,true,true,false] [false,true,false,true] 6 local3 n [true] [true]

theorem phase4 (n : Nat) : run0 table 13 ⟨1,[true,true,true,false,true,true,true,false,true],(rep [false,true,false,true] (n)) ++ ([true])⟩ = some ⟨0,[],([true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true]) = ([true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([false,true,false,true,true]) := by
  calc
    _ = ([true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,false,true,false,true,false,true,false] [true] [false,true,false] true n
    _ = ([true,false,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,false,true,false,true,false,true] [true,true] [true,false,true] false n
    _ = ([true,false,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,false,true,false,true,false] [false,true,true] [false,true,false] true n
    _ = ([true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([false,true,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [true,false,true,false,true] [true,false,true,true] [true,false,true] false n

theorem growth (n : Nat) : run0 table (26+10*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 4+4*n+9+6*n+13=26+10*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 15 (fun n => 26+10*n) entry (by intro n; omega) growth m hm

#print axioms never

end M13846

namespace M13913

-- 1RB0LA_1RC1LB_0RD1LA_1LD1RE_1RF1RE_1LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true]),[]⟩

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨4,([false]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true]),[]⟩ = some ⟨1,([true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true]),[true]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 8 ⟨1,([true]) ++ ([true,true,true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨1,([true]) ++ (L),([true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (8*n) ⟨1,([true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true]),[true]⟩ = some ⟨1,[true,true,true,true,true],(rep [true,true,true,true,true,true,true,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true] [] [true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] 8 local1 n [true,true,true,true] [true]

theorem phase2 (n : Nat) : run0 table 17 ⟨1,[true,true,true,true,true],(rep [true,true,true,true,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨4,[true,true,false,true,true],([true,true,true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 8 ⟨4,([true]) ++ (L),([true,true,true]) ++ ([true,true,true,true,true,true,true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true,true,true,true,true,true,true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (8*n) ⟨4,[true,true,false,true,true],([true,true,true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨4,([true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true,false,true,true]),[true,true,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true,true,true] [true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] 8 local3 n [true,false,true,true] [true]

theorem phase4 (n : Nat) : run0 table 7 ⟨4,([true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true,false,true,true]),[true,true,true,true]⟩ = some ⟨1,([true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true,false,true,true]),[true]⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 8 ⟨1,([true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨1,([true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (8*n) ⟨1,([true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true,false,true,true]),[true]⟩ = some ⟨1,[true,true,true,true,true,true,true,false,true,true],(rep [true,true,true,true,true,true,true,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] 8 local5 n [true,false,true,true] [true]

theorem phase6 (n : Nat) : run0 table 18 ⟨1,[true,true,true,true,true,true,true,false,true,true],(rep [true,true,true,true,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨4,[true,true,true],([true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 8 ⟨4,([true]) ++ (L),([true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true,true,true,true,true,true,true]) ++ (L),([true,true,true,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (8*n) ⟨4,[true,true,true],([true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨4,([true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true,true]),[true,true,true,true,true,true,true,true,true]⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] 8 local7 n [true,true] [true]

theorem phase8 (n : Nat) : run0 table 10 ⟨4,([true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true,true]),[true,true,true,true,true,true,true,true,true]⟩ = some ⟨4,([false,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true,true]) = ([false,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true]) := by
  calc
    _ = ([false,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true,true,true,true] [true,true] [true,true,true,true,true,true,true] true n
    _ = ([false,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut [false,true,true,true,true,true,true,true,true] [true,true,true] [true,true,true,true,true,true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (54+32*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalL n] at H
  rw [show 2+8*n+17+8*n+7+8*n+18+8*n+10=54+32*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (fun n => 54+32*n) entry (by intro n; omega) growth m hm

#print axioms never

end M13913

namespace M2380

-- 1RB1LA_1RC0RF_0RD1LF_1LD1RE_0LF1RE_---0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,[],([true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,true,false]) ++ (rep [false,false] (n)) ++ ([false])⟩

theorem entry : run0 table 47 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 16 ⟨0,[],([true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,true,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ = some ⟨4,([true,true,false,true,true,true]),(rep [true,true] (n)) ++ ([true,true,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨4,([true]) ++ (L),([true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true]) ++ (L),(R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨4,([true,true,false,true,true,true]),(rep [true,true] (n)) ++ ([true,true,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ = some ⟨4,([true]) ++ (rep [true,true] (n)) ++ ([true,false,true,true,true]),([true,true,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [] [true,true] [true,true] 2 local1 n (([true,false,true,true,true])) (([true,true,false]) ++ (rep [false,false] (n)) ++ ([false]))

theorem phase2 (n : Nat) : run0 table 5 ⟨4,([true]) ++ (rep [true,true] (n)) ++ ([true,false,true,true,true]),([true,true,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ = some ⟨0,([true,true]) ++ (rep [true,true] (n)) ++ ([true,false,true,true,true]),([false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 2 ⟨0,([true,true]) ++ ([true,true]) ++ (L),(R)⟩ = some ⟨0,([true,true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (2*n) ⟨0,([true,true]) ++ (rep [true,true] (n)) ++ ([true,false,true,true,true]),([false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ = some ⟨0,([true,true,true,false,true,true,true]),(rep [true,true] (n)) ++ ([false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,true] [] [true,true] [true,true] 2 local3 n (([true,false,true,true,true])) (([false,false]) ++ (rep [false,false] (n)) ++ ([false]))

theorem phase4 (n : Nat) : run0 table 46 ⟨0,([true,true,true,false,true,true,true]),(rep [true,true] (n)) ++ ([false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ = some ⟨4,([true,true,true,true,true,true,true]),([true,true]) ++ (rep [true,true] (n)) ++ ([false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 2 ⟨4,([true]) ++ (L),([true,true]) ++ ([true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (2*n) ⟨4,([true,true,true,true,true,true,true]),([true,true]) ++ (rep [true,true] (n)) ++ ([false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ = some ⟨4,([true]) ++ (rep [true,true] (n)) ++ ([true,true,true,true,true,true]),([true,true,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true,true] [true,true] [true,true] 2 local5 n (([true,true,true,true,true,true])) (([false,false]) ++ (rep [false,false] (n)) ++ ([false]))

theorem phase6 (n : Nat) : run0 table 5 ⟨4,([true]) ++ (rep [true,true] (n)) ++ ([true,true,true,true,true,true]),([true,true,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ = some ⟨0,([true,true]) ++ (rep [true,true] (n)) ++ ([true,true,true,true,true,true]),([false,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 2 ⟨0,([true,true]) ++ ([true,true]) ++ (L),(R)⟩ = some ⟨0,([true,true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (2*n) ⟨0,([true,true]) ++ (rep [true,true] (n)) ++ ([true,true,true,true,true,true]),([false,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ = some ⟨0,([true,true,true,true,true,true,true,true]),(rep [true,true] (n)) ++ ([false,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,true] [] [true,true] [true,true] 2 local7 n (([true,true,true,true,true,true])) (([false,false,false]) ++ (rep [false,false] (n)) ++ ([false]))

theorem phase8 (n : Nat) : run0 table 8 ⟨0,([true,true,true,true,true,true,true,true]),(rep [true,true] (n)) ++ ([false,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ = some ⟨0,[],([true,true,true,true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,true,true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false,false,false]) ++ (rep [false,false] (n)) ++ ([false]) = ([true,true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,true,false,false,false]) ++ (rep [false,false] (n)) ++ ([false]) := by
  calc
    _ = ([true,true,true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,false,false,false]) ++ (rep [false,false] (n)) ++ ([false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true,true,true,true,true,true])) (([false,false,false]) ++ (rep [false,false] (n)) ++ ([false])) [true] true n
    _ = ([true,true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([true,true,false,false,false]) ++ (rep [false,false] (n)) ++ ([false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true,true,true,true,true])) (([true,false,false,false]) ++ (rep [false,false] (n)) ++ ([false])) [true] true n

theorem growth (n : Nat) : run0 table (80+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalR n] at H
  rw [show 16+2*n+5+2*n+46+2*n+5+2*n+8=80+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 47 (fun n => 80+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M2380

namespace M4022

-- 1RB1LA_1RC0LF_0RD---_1LD1RE_0RF1RE_0LF0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,[],([true,true,true]) ++ (rep [true,true] (n)) ++ ([false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨0,[],([true,true,true]) ++ (rep [true,true] (n)) ++ ([false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ = some ⟨4,([true,true,false,true,true]),(rep [true,true] (n)) ++ ([false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨4,([true]) ++ (L),([true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true]) ++ (L),(R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨4,([true,true,false,true,true]),(rep [true,true] (n)) ++ ([false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ = some ⟨4,([true]) ++ (rep [true,true] (n)) ++ ([true,false,true,true]),([false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [] [true,true] [true,true] 2 local1 n (([true,false,true,true])) (([false,false]) ++ (rep [false,false] (n)) ++ ([false]))

theorem phase2 (n : Nat) : run0 table 5 ⟨4,([true]) ++ (rep [true,true] (n)) ++ ([true,false,true,true]),([false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ = some ⟨0,(rep [true,true] (n)) ++ ([true,false,true,true]),([false,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 2 ⟨0,([true,true]) ++ (L),(R)⟩ = some ⟨0,(L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (2*n) ⟨0,(rep [true,true] (n)) ++ ([true,false,true,true]),([false,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ = some ⟨0,([true,false,true,true]),(rep [true,true] (n)) ++ ([false,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [] [] [true,true] [true,true] 2 local3 n (([true,false,true,true])) (([false,false,false]) ++ (rep [false,false] (n)) ++ ([false]))

theorem phase4 (n : Nat) : run0 table 23 ⟨0,([true,false,true,true]),(rep [true,true] (n)) ++ ([false,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ = some ⟨4,([true,true,true,true,true]),([true]) ++ (rep [true,true] (n)) ++ ([false,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 2 ⟨4,([true]) ++ (L),([true]) ++ ([true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (2*n) ⟨4,([true,true,true,true,true]),([true]) ++ (rep [true,true] (n)) ++ ([false,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ = some ⟨4,([true]) ++ (rep [true,true] (n)) ++ ([true,true,true,true]),([true,false,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true] [true,true] [true,true] 2 local5 n (([true,true,true,true])) (([false,false,false]) ++ (rep [false,false] (n)) ++ ([false]))

theorem phase6 (n : Nat) : run0 table 6 ⟨4,([true]) ++ (rep [true,true] (n)) ++ ([true,true,true,true]),([true,false,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ = some ⟨0,([true]) ++ (rep [true,true] (n)) ++ ([true,true,true,true]),([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 2 ⟨0,([true]) ++ ([true,true]) ++ (L),(R)⟩ = some ⟨0,([true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (2*n) ⟨0,([true]) ++ (rep [true,true] (n)) ++ ([true,true,true,true]),([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ = some ⟨0,([true,true,true,true,true]),(rep [true,true] (n)) ++ ([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true] [] [true,true] [true,true] 2 local7 n (([true,true,true,true])) (([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false]))

theorem phase8 (n : Nat) : run0 table 5 ⟨0,([true,true,true,true,true]),(rep [true,true] (n)) ++ ([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ = some ⟨0,[],([true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false]) = ([true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false]) := by
  rfl

theorem growth (n : Nat) : run0 table (46+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 7+2*n+5+2*n+23+2*n+6+2*n+5=46+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 15 (fun n => 46+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M4022

namespace M4665

-- 1RB0LE_1RC1RF_0RD---_1LD1RE_1LA1RE_0LF0RA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨false,true,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [true,false,true,false,true] (n)) ++ ([true]) ++ (rep [false,true,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 13 ⟨1,([false]) ++ (rep [true,false,true,false,true] (n)) ++ ([true]) ++ (rep [false,true,false,true] (n)),[]⟩ = some ⟨4,([false,true]) ++ (rep [true,false,true,false,true] (n)) ++ ([true]) ++ (rep [false,true,false,true] (n)),([true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 7 ⟨4,([false,true]) ++ ([true,false,true,false,true]) ++ (L),(R)⟩ = some ⟨4,([false,true]) ++ (L),([false,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (7*n) ⟨4,([false,true]) ++ (rep [true,false,true,false,true] (n)) ++ ([true]) ++ (rep [false,true,false,true] (n)),([true,true])⟩ = some ⟨4,([false,true,true]) ++ (rep [false,true,false,true] (n)),(rep [false,true,false,true,true] (n)) ++ ([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true] [] [true,false,true,false,true] [false,true,false,true,true] 7 local1 n (([true]) ++ (rep [false,true,false,true] (n))) (([true,true]))

theorem phase2 (n : Nat) : run0 table 3 ⟨4,([false,true,true]) ++ (rep [false,true,false,true] (n)),(rep [false,true,false,true,true] (n)) ++ ([true,true])⟩ = some ⟨4,([false,true]) ++ (rep [false,true,false,true] (n)),([true]) ++ (rep [false,true,false,true,true] (n)) ++ ([true,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 4 ⟨4,([false,true]) ++ ([false,true,false,true]) ++ (L),(R)⟩ = some ⟨4,([false,true]) ++ (L),([false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (4*n) ⟨4,([false,true]) ++ (rep [false,true,false,true] (n)),([true]) ++ (rep [false,true,false,true,true] (n)) ++ ([true,true])⟩ = some ⟨4,([false,true]),(rep [false,true,false,true] (n)) ++ ([true]) ++ (rep [false,true,false,true,true] (n)) ++ ([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true] [] [false,true,false,true] [false,true,false,true] 4 local3 n ([]) (([true]) ++ (rep [false,true,false,true,true] (n)) ++ ([true,true]))

theorem phase4 (n : Nat) : run0 table 4 ⟨4,([false,true]),(rep [false,true,false,true] (n)) ++ ([true]) ++ (rep [false,true,false,true,true] (n)) ++ ([true,true])⟩ = some ⟨1,([true,true]),([false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true]) ++ (rep [false,true,false,true,true] (n)) ++ ([true,true])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 8 ⟨1,([true]) ++ (L),([false,true]) ++ ([false,true,false,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true,false]) ++ (L),([false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (8*n) ⟨1,([true,true]),([false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true]) ++ (rep [false,true,false,true,true] (n)) ++ ([true,true])⟩ = some ⟨1,([true]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false,true,true]) ++ (rep [false,true,false,true,true] (n)) ++ ([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,true] [false,true,false,true] [true,false,true,false] 8 local5 n (([true])) (([true]) ++ (rep [false,true,false,true,true] (n)) ++ ([true,true]))

theorem local6 (L R : List Bool) : run0 table 7 ⟨1,([true]) ++ (L),([false,true,true]) ++ ([false,true,false,true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true,true,false]) ++ (L),([false,true,true]) ++ (R)⟩ := by rfl

theorem phase6 (n : Nat) : run0 table (7*n) ⟨1,([true]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false,true,true]) ++ (rep [false,true,false,true,true] (n)) ++ ([true,true])⟩ = some ⟨1,([true]) ++ (rep [true,false,true,true,false] (n)) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,true,true] [false,true,false,true,true] [true,false,true,true,false] 7 local6 n ((rep [true,false,true,false] (n)) ++ ([true])) (([true,true]))

theorem phase7 (n : Nat) : run0 table 6 ⟨1,([true]) ++ (rep [true,false,true,true,false] (n)) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false,true,true,true,true])⟩ = some ⟨0,([true,false,true,true,false]) ++ (rep [true,false,true,true,false] (n)) ++ (rep [true,false,true,false] (n)) ++ ([true]),([true])⟩ := by rfl

theorem local8 (L R : List Bool) : run0 table 7 ⟨0,([true,false,true,true,false]) ++ ([true,false,true,true,false]) ++ (L),(R)⟩ = some ⟨0,([true,false,true,true,false]) ++ (L),([true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase8 (n : Nat) : run0 table (7*n) ⟨0,([true,false,true,true,false]) ++ (rep [true,false,true,true,false] (n)) ++ (rep [true,false,true,false] (n)) ++ ([true]),([true])⟩ = some ⟨0,([true,false,true,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),(rep [true,false,true,true,false] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,false,true,true,false] [] [true,false,true,true,false] [true,false,true,true,false] 7 local8 n ((rep [true,false,true,false] (n)) ++ ([true])) (([true]))

theorem phase9 (n : Nat) : run0 table 4 ⟨0,([true,false,true,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),(rep [true,false,true,true,false] (n)) ++ ([true])⟩ = some ⟨4,([false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([true,false]) ++ (rep [true,false,true,true,false] (n)) ++ ([true])⟩ := by rfl

theorem local10 (L R : List Bool) : run0 table 4 ⟨4,([false,true,false]) ++ ([true,false,true,false]) ++ (L),(R)⟩ = some ⟨4,([false,true,false]) ++ (L),([false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase10 (n : Nat) : run0 table (4*n) ⟨4,([false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([true,false]) ++ (rep [true,false,true,true,false] (n)) ++ ([true])⟩ = some ⟨4,([false,true,false,true]),(rep [false,true,false,true] (n)) ++ ([true,false]) ++ (rep [true,false,true,true,false] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,false] [] [true,false,true,false] [false,true,false,true] 4 local10 n (([true])) (([true,false]) ++ (rep [true,false,true,true,false] (n)) ++ ([true]))

theorem phase11 (n : Nat) : run0 table 6 ⟨4,([false,true,false,true]),(rep [false,true,false,true] (n)) ++ ([true,false]) ++ (rep [true,false,true,true,false] (n)) ++ ([true])⟩ = some ⟨1,([true,true]),([false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false]) ++ (rep [true,false,true,true,false] (n)) ++ ([true])⟩ := by rfl

theorem local12 (L R : List Bool) : run0 table 8 ⟨1,([true]) ++ (L),([false,true,false,true]) ++ ([false,true,false,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true,false]) ++ (L),([false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase12 (n : Nat) : run0 table (8*n) ⟨1,([true,true]),([false,true,false,true]) ++ (rep [false,true,false,true] (n)) ++ ([true,false]) ++ (rep [true,false,true,true,false] (n)) ++ ([true])⟩ = some ⟨1,([true]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false,true,false,true,true,false]) ++ (rep [true,false,true,true,false] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,true,false,true] [false,true,false,true] [true,false,true,false] 8 local12 n (([true])) (([true,false]) ++ (rep [true,false,true,true,false] (n)) ++ ([true]))

theorem phase13 (n : Nat) : run0 table 2 ⟨1,([true]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false,true,false,true,true,false]) ++ (rep [true,false,true,true,false] (n)) ++ ([true])⟩ = some ⟨5,([true]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false,true,false,true,true,false]) ++ (rep [true,false,true,true,false] (n)) ++ ([true])⟩ := by rfl

theorem local14 (L R : List Bool) : run0 table 7 ⟨5,([true]) ++ (L),([false,true,false,true,true,false]) ++ ([true,false,true,true,false]) ++ (R)⟩ = some ⟨5,([true]) ++ ([true,true,false,true,false]) ++ (L),([false,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase14 (n : Nat) : run0 table (7*n) ⟨5,([true]) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false,true,false,true,true,false]) ++ (rep [true,false,true,true,false] (n)) ++ ([true])⟩ = some ⟨5,([true]) ++ (rep [true,true,false,true,false] (n)) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false,true,false,true,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 5 [true] [false,true,false,true,true,false] [true,false,true,true,false] [true,true,false,true,false] 7 local14 n ((rep [true,false,true,false] (n)) ++ ([true])) (([true]))

theorem phase15 (n : Nat) : run0 table 13 ⟨5,([true]) ++ (rep [true,true,false,true,false] (n)) ++ (rep [true,false,true,false] (n)) ++ ([true]),([false,true,false,true,true,false,true])⟩ = some ⟨1,([false,true,false,true,false,true,true,false,true,false]) ++ (rep [true,true,false,true,false] (n)) ++ (rep [true,false,true,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,true,false,true,true,false,true,false]) ++ (rep [true,true,false,true,false] (n)) ++ (rep [true,false,true,false] (n)) ++ ([true]) = ([false,true,false,true,false,true]) ++ (rep [true,false,true,false,true] (n)) ++ ([true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) := by
  calc
    _ = ([false,true,false,true,false,true,true,false,true]) ++ (rep [false,true,true,false,true] (n)) ++ ([false]) ++ (rep [true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,false,true,true,false,true])) ((rep [true,false,true,false] (n)) ++ ([true])) [true,true,false,true] false n
    _ = ([false,true,false,true,false,true,true,false]) ++ (rep [true,false,true,true,false] (n)) ++ ([true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,false,true,true,false])) (([false]) ++ (rep [true,false,true,false] (n)) ++ ([true])) [false,true,true,false] true n
    _ = ([false,true,false,true,false,true,true]) ++ (rep [false,true,false,true,true] (n)) ++ ([false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,false,true,true])) (([true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true])) [true,false,true,true] false n
    _ = ([false,true,false,true,false,true]) ++ (rep [true,false,true,false,true] (n)) ++ ([true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,false,true])) (([false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true])) [false,true,false,true] true n
    _ = ([false,true,false,true,false]) ++ (rep [true,true,false,true,false] (n)) ++ ([true,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,false])) (([true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true])) [true,false,true,false] true n
    _ = ([false,true,false,true]) ++ (rep [false,true,true,false,true] (n)) ++ ([false,true,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true])) (([true,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true])) [true,true,false,true] false n
    _ = ([false,true,false]) ++ (rep [true,false,true,true,false] (n)) ++ ([true,false,true,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false])) (([false,true,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true])) [false,true,true,false] true n
    _ = ([false,true]) ++ (rep [false,true,false,true,true] (n)) ++ ([false,true,false,true,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([true,false,true,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true])) [true,false,true,true] false n
    _ = ([false]) ++ (rep [true,false,true,false,true] (n)) ++ ([true,false,true,false,true,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,true,false,true,true,false,true,false]) ++ (rep [true,false,true,false] (n)) ++ ([true])) [false,true,false,true] true n
    _ = ([false]) ++ (rep [true,false,true,false,true] (n)) ++ ([true,false,true,false,true,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false]) ++ (rep [true,false,true,false,true] (n)) ++ ([true,false,true,false,true,true,false,true,false])) ([]) [false,true,false] true n
    _ = ([false,true]) ++ (rep [false,true,false,true,true] (n)) ++ ([false,true,false,true,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,true,false,true,true,false,true,false,true]) ++ (rep [false,true,false,true] (n))) [false,true,false,true] true n
    _ = ([false,true,false]) ++ (rep [true,false,true,true,false] (n)) ++ ([true,false,true,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([true,false,true,true,false,true,false,true]) ++ (rep [false,true,false,true] (n))) [true,false,true,true] false n
    _ = ([false,true,false,true]) ++ (rep [false,true,true,false,true] (n)) ++ ([false,true,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false])) (([false,true,true,false,true,false,true]) ++ (rep [false,true,false,true] (n))) [false,true,true,false] true n
    _ = ([false,true,false,true,false]) ++ (rep [true,true,false,true,false] (n)) ++ ([true,true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true])) (([true,true,false,true,false,true]) ++ (rep [false,true,false,true] (n))) [true,true,false,true] false n
    _ = ([false,true,false,true,false,true]) ++ (rep [true,false,true,false,true] (n)) ++ ([true,false,true,false,true]) ++ (rep [false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,false])) (([true,false,true,false,true]) ++ (rep [false,true,false,true] (n))) [true,false,true,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (51+52*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n)) (phase9 n)) (phase10 n)) (phase11 n)) (phase12 n)) (phase13 n)) (phase14 n)) (phase15 n))
  rw [finalL n] at H
  rw [show 13+7*n+3+4*n+4+8*n+7*n+6+7*n+4+4*n+6+8*n+2+7*n+13=51+52*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 51+52*n) entry (by intro n; omega) growth m hm

#print axioms never

end M4665

namespace M4842

-- 1RB0LF_1RC0RC_0RD0RB_1LD1RE_1LA1RE_---1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false]) ++ (rep [false,false] (n)) ++ ([true,false,false]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]),[]⟩

theorem entry : run0 table 30 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨2,([false]) ++ (rep [false,false] (n)) ++ ([true,false,false]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]),[]⟩ = some ⟨3,([false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨3,([false,false]) ++ ([false,false]) ++ (L),(R)⟩ = some ⟨3,([false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨3,([false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]),[]⟩ = some ⟨3,([false,false,true,false,false]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]),(rep [true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false] [] [false,false] [true,true] 2 local1 n (([true,false,false]) ++ (rep [true] (n)) ++ ([false,true,false,false,true])) ([])

theorem phase2 (n : Nat) : run0 table 3 ⟨3,([false,false,true,false,false]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]),(rep [true,true] (n))⟩ = some ⟨4,([true,true,false,false]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]),([true]) ++ (rep [true,true] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 2 ⟨4,([true]) ++ (L),([true]) ++ ([true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (2*n) ⟨4,([true,true,false,false]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]),([true]) ++ (rep [true,true] (n))⟩ = some ⟨4,([true]) ++ (rep [true,true] (n)) ++ ([true,false,false]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true] [true,true] [true,true] 2 local3 n (([true,false,false]) ++ (rep [true] (n)) ++ ([false,true,false,false,true])) ([])

theorem phase4 (n : Nat) : run0 table 2 ⟨4,([true]) ++ (rep [true,true] (n)) ++ ([true,false,false]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]),([true])⟩ = some ⟨4,([false,true,true]) ++ (rep [true,true] (n)) ++ ([true,false,false]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]),[]⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 10 ⟨4,([false,true,true]) ++ ([true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (10*n) ⟨4,([false,true,true]) ++ (rep [true,true] (n)) ++ ([true,false,false]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]),[]⟩ = some ⟨4,([false,true,true,true,false,false]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]),(rep [true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true] [] [true,true] [true,true] 10 local5 n (([true,false,false]) ++ (rep [true] (n)) ++ ([false,true,false,false,true])) ([])

theorem phase6 (n : Nat) : run0 table 13 ⟨4,([false,true,true,true,false,false]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]),(rep [true,true] (n))⟩ = some ⟨2,([true,true,false,false,true]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]),([true]) ++ (rep [true,true] (n))⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 2 ⟨2,([true]) ++ (L),([true]) ++ ([true,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([false,false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (2*n) ⟨2,([true,true,false,false,true]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]),([true]) ++ (rep [true,true] (n))⟩ = some ⟨2,([true]) ++ (rep [false,false] (n)) ++ ([true,false,false,true]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true] [true,true] [false,false] 2 local7 n (([true,false,false,true]) ++ (rep [true] (n)) ++ ([false,true,false,false,true])) ([])

theorem phase8 (n : Nat) : run0 table 2 ⟨2,([true]) ++ (rep [false,false] (n)) ++ ([true,false,false,true]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]),([true])⟩ = some ⟨2,([false,false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false,true]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false,true]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]) = ([false,false,false]) ++ (rep [false,false] (n)) ++ ([true,false,false,true]) ++ (rep [true] (n)) ++ ([false,true,false,false,true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (21+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 1+2*n+3+2*n+2+10*n+13+2*n+2=21+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 30 (fun n => 21+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M4842

namespace M4850

-- 1RB0LF_1RC1LB_0RD0RB_1LD1RE_1LA1RE_---1LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [false,true,true] (n)) ++ (rep [true,false,true,true] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 12 ⟨1,([false]) ++ (rep [false,true,true] (n)) ++ (rep [true,false,true,true] (n)) ++ ([true]),[]⟩ = some ⟨4,([false,true,true]) ++ (rep [false,true,true] (n)) ++ (rep [true,false,true,true] (n)) ++ ([true]),([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨4,([false,true,true]) ++ ([false,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true]) ++ (L),([true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨4,([false,true,true]) ++ (rep [false,true,true] (n)) ++ (rep [true,false,true,true] (n)) ++ ([true]),([true])⟩ = some ⟨4,([false,true,true]) ++ (rep [true,false,true,true] (n)) ++ ([true]),(rep [true,false,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true] [] [false,true,true] [true,false,true] 3 local1 n ((rep [true,false,true,true] (n)) ++ ([true])) (([true]))

theorem local2 (L R : List Bool) : run0 table 8 ⟨4,([false,true,true]) ++ ([true,false,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true]) ++ (L),([true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (8*n) ⟨4,([false,true,true]) ++ (rep [true,false,true,true] (n)) ++ ([true]),(rep [true,false,true] (n)) ++ ([true])⟩ = some ⟨4,([false,true,true,true]),(rep [true,false,true,true] (n)) ++ (rep [true,false,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true] [] [true,false,true,true] [true,false,true,true] 8 local2 n (([true])) ((rep [true,false,true] (n)) ++ ([true]))

theorem phase3 (n : Nat) : run0 table 13 ⟨4,([false,true,true,true]),(rep [true,false,true,true] (n)) ++ (rep [true,false,true] (n)) ++ ([true])⟩ = some ⟨2,([true,true]),([true,true,false,true,true]) ++ (rep [true,false,true,true] (n)) ++ (rep [true,false,true] (n)) ++ ([true])⟩ := by rfl

theorem local4 (L R : List Bool) : run0 table 8 ⟨2,([true]) ++ (L),([true,true,false,true,true]) ++ ([true,false,true,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,false,true,true]) ++ (L),([true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase4 (n : Nat) : run0 table (8*n) ⟨2,([true,true]),([true,true,false,true,true]) ++ (rep [true,false,true,true] (n)) ++ (rep [true,false,true] (n)) ++ ([true])⟩ = some ⟨2,([true]) ++ (rep [true,false,true,true] (n)) ++ ([true]),([true,true,false,true,true]) ++ (rep [true,false,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true,true,false,true,true] [true,false,true,true] [true,false,true,true] 8 local4 n (([true])) ((rep [true,false,true] (n)) ++ ([true]))

theorem phase5 (n : Nat) : run0 table 10 ⟨2,([true]) ++ (rep [true,false,true,true] (n)) ++ ([true]),([true,true,false,true,true]) ++ (rep [true,false,true] (n)) ++ ([true])⟩ = some ⟨1,([false,true,false,true,true]) ++ (rep [true,false,true,true] (n)) ++ ([true]),([true]) ++ (rep [true,false,true] (n)) ++ ([true])⟩ := by rfl

theorem local6 (L R : List Bool) : run0 table 5 ⟨1,([false]) ++ (L),([true]) ++ ([true,false,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,true,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase6 (n : Nat) : run0 table (5*n) ⟨1,([false,true,false,true,true]) ++ (rep [true,false,true,true] (n)) ++ ([true]),([true]) ++ (rep [true,false,true] (n)) ++ ([true])⟩ = some ⟨1,([false]) ++ (rep [false,true,true] (n)) ++ ([true,false,true,true]) ++ (rep [true,false,true,true] (n)) ++ ([true]),([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true] [true,false,true] [false,true,true] 5 local6 n (([true,false,true,true]) ++ (rep [true,false,true,true] (n)) ++ ([true])) (([true]))

theorem phase7 (n : Nat) : run0 table 5 ⟨1,([false]) ++ (rep [false,true,true] (n)) ++ ([true,false,true,true]) ++ (rep [true,false,true,true] (n)) ++ ([true]),([true,true])⟩ = some ⟨1,([false,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,false,true,true]) ++ (rep [true,false,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,false,true,true]) ++ (rep [true,false,true,true] (n)) ++ ([true]) = ([false,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,false,true,true]) ++ (rep [true,false,true,true] (n)) ++ ([true]) := by
  rfl

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (40+24*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n))
  rw [show 12+3*n+8*n+13+8*n+10+5*n+5=40+24*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 40+24*n) entry (by intro n; omega) growth m hm

#print axioms never

end M4850

namespace M6748

-- 1RB1LE_1RC0LA_0RD1RF_1LD1RE_1LB1RE_---0RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,([false,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true]),[]⟩

theorem entry : run0 table 31 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 11 ⟨2,([false,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true]),[]⟩ = some ⟨4,([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true]),([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨4,([false,true,true]) ++ ([false,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true]) ++ (L),([true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨4,([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true]),([true])⟩ = some ⟨4,([false,true,true,true,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true]),(rep [true,false,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true] [] [false,true,true] [true,false,true] 3 local1 n (([true,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true])) (([true]))

theorem phase2 (n : Nat) : run0 table 15 ⟨4,([false,true,true,true,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true]),(rep [true,false,true] (n)) ++ ([true])⟩ = some ⟨4,([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true]),([true,true,true]) ++ (rep [true,false,true] (n)) ++ ([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨4,([false,true,true]) ++ ([false,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true]) ++ (L),([true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨4,([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true]),([true,true,true]) ++ (rep [true,false,true] (n)) ++ ([true])⟩ = some ⟨4,([false,true,true,false,true,true]),(rep [true,false,true] (n)) ++ ([true,true,true]) ++ (rep [true,false,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true] [] [false,true,true] [true,false,true] 3 local3 n (([false,true,true])) (([true,true,true]) ++ (rep [true,false,true] (n)) ++ ([true]))

theorem phase4 (n : Nat) : run0 table 8 ⟨4,([false,true,true,false,true,true]),(rep [true,false,true] (n)) ++ ([true,true,true]) ++ (rep [true,false,true] (n)) ++ ([true])⟩ = some ⟨2,([true,true]),([true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,true,true]) ++ (rep [true,false,true] (n)) ++ ([true])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 3 ⟨2,([true]) ++ (L),([true,false,true,true,false,true]) ++ ([true,false,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,false,true]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (3*n) ⟨2,([true,true]),([true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,true,true]) ++ (rep [true,false,true] (n)) ++ ([true])⟩ = some ⟨2,([true]) ++ (rep [true,false,true] (n)) ++ ([true]),([true,false,true,true,false,true,true,true,true]) ++ (rep [true,false,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [true,false,true,true,false,true] [true,false,true] [true,false,true] 3 local5 n (([true])) (([true,true,true]) ++ (rep [true,false,true] (n)) ++ ([true]))

theorem phase6 (n : Nat) : run0 table 10 ⟨2,([true]) ++ (rep [true,false,true] (n)) ++ ([true]),([true,false,true,true,false,true,true,true,true]) ++ (rep [true,false,true] (n)) ++ ([true])⟩ = some ⟨1,([false,true,true,true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true]),([true]) ++ (rep [true,false,true] (n)) ++ ([true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 3 ⟨1,([false]) ++ (L),([true]) ++ ([true,false,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([false,true,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (3*n) ⟨1,([false,true,true,true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true]),([true]) ++ (rep [true,false,true] (n)) ++ ([true])⟩ = some ⟨1,([false]) ++ (rep [false,true,true] (n)) ++ ([true,true,true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true]),([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true] [true,false,true] [false,true,true] 3 local7 n (([true,true,true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true])) (([true]))

theorem phase8 (n : Nat) : run0 table 4 ⟨1,([false]) ++ (rep [false,true,true] (n)) ++ ([true,true,true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true]),([true,true])⟩ = some ⟨2,([false,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true]) = ([false,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true]) := by
  calc
    _ = ([false,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,true,true,true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true])) (([true,true,true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true])) [false,true] true n
    _ = ([false,true,false]) ++ (rep [true,true,false] (n)) ++ ([true,true,true,true,true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false])) (([true,true,true,true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true])) [true,false] true n
    _ = ([false,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,true,true,true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([true,true,true,true,true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true])) [true,true] false n
    _ = ([false]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,true,true,true,true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,true,true,true,true,true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true])) [false,true] true n
    _ = ([false]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,true,true,true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,true,true,true,true,false,true,true,false])) (([true])) [true,false] true n
    _ = ([false]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,true,true,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,true,true,true,true,false,true,true])) (([true,true])) [true,true] false n
    _ = ([false,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,true,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,true,true,true,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true])) [false,true] true n
    _ = ([false,true,false]) ++ (rep [true,true,false] (n)) ++ ([true,true,true,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([true,true,true,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true])) [true,true] false n
    _ = ([false,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,true,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false])) (([true,true,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true])) [true,false] true n
    _ = ([false,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true])) (([true,true,true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true])) [false,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (48+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalL n] at H
  rw [show 11+3*n+15+3*n+8+3*n+10+3*n+4=48+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 31 (fun n => 48+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M6748

namespace M7317

-- 1RB0LF_1RC0RA_0RD---_1LD1RE_1LB1RE_1LA0LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false]) ++ (rep [true,false,true,true] (n)) ++ ([true]) ++ (rep [false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 10 ⟨1,([false]) ++ (rep [true,false,true,true] (n)) ++ ([true]) ++ (rep [false,true] (n)),[]⟩ = some ⟨5,([false,true,true]) ++ (rep [true,false,true,true] (n)) ++ ([true]) ++ (rep [false,true] (n)),([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨5,([false,true,true]) ++ ([true,false,true,true]) ++ (L),(R)⟩ = some ⟨5,([false,true,true]) ++ (L),([false,false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨5,([false,true,true]) ++ (rep [true,false,true,true] (n)) ++ ([true]) ++ (rep [false,true] (n)),([false])⟩ = some ⟨5,([false,true,true,true]) ++ (rep [false,true] (n)),(rep [false,false,false,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,true,true] [] [true,false,true,true] [false,false,false,true] 4 local1 n (([true]) ++ (rep [false,true] (n))) (([false]))

theorem phase2 (n : Nat) : run0 table 4 ⟨5,([false,true,true,true]) ++ (rep [false,true] (n)),(rep [false,false,false,true] (n)) ++ ([false])⟩ = some ⟨5,(rep [false,true] (n)),([false,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 2 ⟨5,([false,true]) ++ (L),(R)⟩ = some ⟨5,(L),([false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (2*n) ⟨5,(rep [false,true] (n)),([false,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([false])⟩ = some ⟨5,[],(rep [false,true] (n)) ++ ([false,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [] [] [false,true] [false,true] 2 local3 n ([]) (([false,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([false]))

theorem phase4 (n : Nat) : run0 table 2 ⟨5,[],(rep [false,true] (n)) ++ ([false,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([false])⟩ = some ⟨1,([true,true]),(rep [false,true] (n)) ++ ([false,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 2 ⟨1,([true]) ++ (L),([false,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false]) ++ (L),(R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (2*n) ⟨1,([true,true]),(rep [false,true] (n)) ++ ([false,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([false])⟩ = some ⟨1,([true]) ++ (rep [true,false] (n)) ++ ([true]),([false,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [] [false,true] [true,false] 2 local5 n (([true])) (([false,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([false]))

theorem local6 (L R : List Bool) : run0 table 10 ⟨1,([true]) ++ (L),([false,false,false,true]) ++ ([false,false,false,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,true,true,false]) ++ (L),([false,false,false,true]) ++ (R)⟩ := by rfl

theorem phase6 (n : Nat) : run0 table (10*n) ⟨1,([true]) ++ (rep [true,false] (n)) ++ ([true]),([false,false,false,true]) ++ (rep [false,false,false,true] (n)) ++ ([false])⟩ = some ⟨1,([true]) ++ (rep [true,true,true,false] (n)) ++ (rep [true,false] (n)) ++ ([true]),([false,false,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,false,false,true] [false,false,false,true] [true,true,true,false] 10 local6 n ((rep [true,false] (n)) ++ ([true])) (([false]))

theorem phase7 (n : Nat) : run0 table 12 ⟨1,([true]) ++ (rep [true,true,true,false] (n)) ++ (rep [true,false] (n)) ++ ([true]),([false,false,false,true,false])⟩ = some ⟨1,([false,true,false,true,true,true,false]) ++ (rep [true,true,true,false] (n)) ++ (rep [true,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,true,true,true,false]) ++ (rep [true,true,true,false] (n)) ++ (rep [true,false] (n)) ++ ([true]) = ([false,true,false,true,true]) ++ (rep [true,false,true,true] (n)) ++ ([true,false,true]) ++ (rep [false,true] (n)) := by
  calc
    _ = ([false,true,false,true,true,true]) ++ (rep [false,true,true,true] (n)) ++ ([false]) ++ (rep [true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,true,true])) ((rep [true,false] (n)) ++ ([true])) [true,true,true] false n
    _ = ([false,true,false,true,true]) ++ (rep [true,false,true,true] (n)) ++ ([true,false]) ++ (rep [true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,true])) (([false]) ++ (rep [true,false] (n)) ++ ([true])) [false,true,true] true n
    _ = ([false,true,false,true]) ++ (rep [true,true,false,true] (n)) ++ ([true,true,false]) ++ (rep [true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true])) (([true,false]) ++ (rep [true,false] (n)) ++ ([true])) [true,false,true] true n
    _ = ([false,true,false]) ++ (rep [true,true,true,false] (n)) ++ ([true,true,true,false]) ++ (rep [true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false])) (([true,true,false]) ++ (rep [true,false] (n)) ++ ([true])) [true,true,false] true n
    _ = ([false,true]) ++ (rep [false,true,true,true] (n)) ++ ([false,true,true,true,false]) ++ (rep [true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([true,true,true,false]) ++ (rep [true,false] (n)) ++ ([true])) [true,true,true] false n
    _ = ([false]) ++ (rep [true,false,true,true] (n)) ++ ([true,false,true,true,true,false]) ++ (rep [true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,true,true,true,false]) ++ (rep [true,false] (n)) ++ ([true])) [false,true,true] true n
    _ = ([false]) ++ (rep [true,false,true,true] (n)) ++ ([true,false,true,true,true,false,true]) ++ (rep [false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false]) ++ (rep [true,false,true,true] (n)) ++ ([true,false,true,true,true,false])) ([]) [false] true n
    _ = ([false,true]) ++ (rep [false,true,true,true] (n)) ++ ([false,true,true,true,false,true]) ++ (rep [false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,true,true,true,false,true]) ++ (rep [false,true] (n))) [false,true,true] true n
    _ = ([false,true,false]) ++ (rep [true,true,true,false] (n)) ++ ([true,true,true,false,true]) ++ (rep [false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([true,true,true,false,true]) ++ (rep [false,true] (n))) [true,true,true] false n
    _ = ([false,true,false,true]) ++ (rep [true,true,false,true] (n)) ++ ([true,true,false,true]) ++ (rep [false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false])) (([true,true,false,true]) ++ (rep [false,true] (n))) [true,true,false] true n
    _ = ([false,true,false,true,true]) ++ (rep [true,false,true,true] (n)) ++ ([true,false,true]) ++ (rep [false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true])) (([true,false,true]) ++ (rep [false,true] (n))) [true,false,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (28+18*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n))
  rw [finalL n] at H
  rw [show 10+4*n+4+2*n+2+2*n+10*n+12=28+18*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 28+18*n) entry (by intro n; omega) growth m hm

#print axioms never

end M7317

namespace M9756

-- 1RB1LA_1RC0RF_0RD0LF_1LD1RE_1LF1RE_---0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,[],([true,true,true]) ++ (rep [true] (n)) ++ ([false]) ++ (rep [true] (n)) ++ ([true])⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 18 ⟨0,[],([true,true,true]) ++ (rep [true] (n)) ++ ([false]) ++ (rep [true] (n)) ++ ([true])⟩ = some ⟨4,([true,true,true,true]),([true]) ++ (rep [true] (n)) ++ ([false]) ++ (rep [true] (n)) ++ ([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 1 ⟨4,([true]) ++ (L),([true]) ++ ([true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (1*n) ⟨4,([true,true,true,true]),([true]) ++ (rep [true] (n)) ++ ([false]) ++ (rep [true] (n)) ++ ([true])⟩ = some ⟨4,([true]) ++ (rep [true] (n)) ++ ([true,true,true]),([true,false]) ++ (rep [true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true] [true] [true] 1 local1 n (([true,true,true])) (([false]) ++ (rep [true] (n)) ++ ([true]))

theorem phase2 (n : Nat) : run0 table 4 ⟨4,([true]) ++ (rep [true] (n)) ++ ([true,true,true]),([true,false]) ++ (rep [true] (n)) ++ ([true])⟩ = some ⟨0,([true]) ++ (rep [true] (n)) ++ ([true,true,true]),([false,true]) ++ (rep [true] (n)) ++ ([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 1 ⟨0,([true]) ++ ([true]) ++ (L),(R)⟩ = some ⟨0,([true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (1*n) ⟨0,([true]) ++ (rep [true] (n)) ++ ([true,true,true]),([false,true]) ++ (rep [true] (n)) ++ ([true])⟩ = some ⟨0,([true,true,true,true]),(rep [true] (n)) ++ ([false,true]) ++ (rep [true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true] [] [true] [true] 1 local3 n (([true,true,true])) (([false,true]) ++ (rep [true] (n)) ++ ([true]))

theorem phase4 (n : Nat) : run0 table 4 ⟨0,([true,true,true,true]),(rep [true] (n)) ++ ([false,true]) ++ (rep [true] (n)) ++ ([true])⟩ = some ⟨0,[],([true,true,true,true]) ++ (rep [true] (n)) ++ ([false,true]) ++ (rep [true] (n)) ++ ([true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,true,true]) ++ (rep [true] (n)) ++ ([false,true]) ++ (rep [true] (n)) ++ ([true]) = ([true,true,true,true]) ++ (rep [true] (n)) ++ ([false,true]) ++ (rep [true] (n)) ++ ([true]) := by
  rfl

theorem growth (n : Nat) : run0 table (26+2*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 18+1*n+4+1*n+4=26+2*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 26+2*n) entry (by intro n; omega) growth m hm

#print axioms never

end M9756

namespace M10315

-- 1RB0RF_1RC0RA_0RD---_1LD1RE_1LF1RE_1LA0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,true] (n)) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 16 ⟨1,([false,true]) ++ (rep [false,true] (n)) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)),[]⟩ = some ⟨4,([false,true]) ++ (rep [false,true] (n)) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)),([true,true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨4,([false,true]) ++ ([false,true]) ++ (L),(R)⟩ = some ⟨4,([false,true]) ++ (L),([false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨4,([false,true]) ++ (rep [false,true] (n)) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)),([true,true,true])⟩ = some ⟨4,([false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)),(rep [false,true] (n)) ++ ([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true] [] [false,true] [false,true] 2 local1 n ((rep [false,true,false,true,false,true,false,true,false,true] (n))) (([true,true,true]))

theorem local2 (L R : List Bool) : run0 table 10 ⟨4,([false,true]) ++ ([false,true,false,true,false,true,false,true,false,true]) ++ (L),(R)⟩ = some ⟨4,([false,true]) ++ (L),([false,true,false,true,false,true,false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (10*n) ⟨4,([false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)),(rep [false,true] (n)) ++ ([true,true,true])⟩ = some ⟨4,([false,true]),(rep [false,true,false,true,false,true,false,true,false,true] (n)) ++ (rep [false,true] (n)) ++ ([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true] [] [false,true,false,true,false,true,false,true,false,true] [false,true,false,true,false,true,false,true,false,true] 10 local2 n ([]) ((rep [false,true] (n)) ++ ([true,true,true]))

theorem phase3 (n : Nat) : run0 table 5 ⟨4,([false,true]),(rep [false,true,false,true,false,true,false,true,false,true] (n)) ++ (rep [false,true] (n)) ++ ([true,true,true])⟩ = some ⟨1,([true,true]),([true,false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)) ++ (rep [false,true] (n)) ++ ([true,true,true])⟩ := by rfl

theorem local4 (L R : List Bool) : run0 table 20 ⟨1,([true]) ++ (L),([true,false,true]) ++ ([false,true,false,true,false,true,false,true,false,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true,false,true,false,true,false,true,false]) ++ (L),([true,false,true]) ++ (R)⟩ := by rfl

theorem phase4 (n : Nat) : run0 table (20*n) ⟨1,([true,true]),([true,false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)) ++ (rep [false,true] (n)) ++ ([true,true,true])⟩ = some ⟨1,([true]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true,false,true]) ++ (rep [false,true] (n)) ++ ([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,false,true] [false,true,false,true,false,true,false,true,false,true] [true,false,true,false,true,false,true,false,true,false] 20 local4 n (([true])) ((rep [false,true] (n)) ++ ([true,true,true]))

theorem local5 (L R : List Bool) : run0 table 4 ⟨1,([true]) ++ (L),([true,false,true]) ++ ([false,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false]) ++ (L),([true,false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (4*n) ⟨1,([true]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true,false,true]) ++ (rep [false,true] (n)) ++ ([true,true,true])⟩ = some ⟨1,([true]) ++ (rep [true,false] (n)) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true,false,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,false,true] [false,true] [true,false] 4 local5 n ((rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) (([true,true,true]))

theorem phase6 (n : Nat) : run0 table 5 ⟨1,([true]) ++ (rep [true,false] (n)) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true,false,true,true,true,true])⟩ = some ⟨0,([true,false,true,false]) ++ (rep [true,false] (n)) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true,true,true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 4 ⟨0,([true,false,true,false]) ++ ([true,false]) ++ (L),([true]) ++ (R)⟩ = some ⟨0,([true,false,true,false]) ++ (L),([true]) ++ ([true,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (4*n) ⟨0,([true,false,true,false]) ++ (rep [true,false] (n)) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true,true,true])⟩ = some ⟨0,([true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true]) ++ (rep [true,false] (n)) ++ ([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,false,true,false] [true] [true,false] [true,false] 4 local7 n ((rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) (([true,true]))

theorem local8 (L R : List Bool) : run0 table 20 ⟨0,([true,false,true,false]) ++ ([true,false,true,false,true,false,true,false,true,false]) ++ (L),([true]) ++ (R)⟩ = some ⟨0,([true,false,true,false]) ++ (L),([true]) ++ ([true,false,true,false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase8 (n : Nat) : run0 table (20*n) ⟨0,([true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true]) ++ (rep [true,false] (n)) ++ ([true,true])⟩ = some ⟨0,([true,false,true,false,true]),([true]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ (rep [true,false] (n)) ++ ([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,false,true,false] [true] [true,false,true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false,true,false] 20 local8 n (([true])) ((rep [true,false] (n)) ++ ([true,true]))

theorem phase9 (n : Nat) : run0 table 13 ⟨0,([true,false,true,false,true]),([true]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ (rep [true,false] (n)) ++ ([true,true])⟩ = some ⟨1,([true,true]),([true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ (rep [true,false] (n)) ++ ([true,true])⟩ := by rfl

theorem local10 (L R : List Bool) : run0 table 20 ⟨1,([true]) ++ (L),([true,false,true,false,true,false]) ++ ([true,false,true,false,true,false,true,false,true,false]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true,false,true,false,true,false,true,false]) ++ (L),([true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase10 (n : Nat) : run0 table (20*n) ⟨1,([true,true]),([true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ (rep [true,false] (n)) ++ ([true,true])⟩ = some ⟨1,([true]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true,false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,false,true,false,true,false] [true,false,true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false,true,false] 20 local10 n (([true])) ((rep [true,false] (n)) ++ ([true,true]))

theorem local11 (L R : List Bool) : run0 table 4 ⟨1,([true]) ++ (L),([true,false,true,false,true,false]) ++ ([true,false]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false]) ++ (L),([true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase11 (n : Nat) : run0 table (4*n) ⟨1,([true]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true,false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true,true])⟩ = some ⟨1,([true]) ++ (rep [true,false] (n)) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true,false,true,false,true,false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,false,true,false,true,false] [true,false] [true,false] 4 local11 n ((rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) (([true,true]))

theorem phase12 (n : Nat) : run0 table 13 ⟨1,([true]) ++ (rep [true,false] (n)) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true,false,true,false,true,false,true,true])⟩ = some ⟨0,([true,false,true,false,true,false,true,false]) ++ (rep [true,false] (n)) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true])⟩ := by rfl

theorem local13 (L R : List Bool) : run0 table 4 ⟨0,([true,false,true,false,true,false,true,false]) ++ ([true,false]) ++ (L),([true]) ++ (R)⟩ = some ⟨0,([true,false,true,false,true,false,true,false]) ++ (L),([true]) ++ ([true,false]) ++ (R)⟩ := by rfl

theorem phase13 (n : Nat) : run0 table (4*n) ⟨0,([true,false,true,false,true,false,true,false]) ++ (rep [true,false] (n)) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true])⟩ = some ⟨0,([true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true]) ++ (rep [true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,false,true,false,true,false,true,false] [true] [true,false] [true,false] 4 local13 n ((rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) ([])

theorem local14 (L R : List Bool) : run0 table 20 ⟨0,([true,false,true,false,true,false,true,false]) ++ ([true,false,true,false,true,false,true,false,true,false]) ++ (L),([true]) ++ (R)⟩ = some ⟨0,([true,false,true,false,true,false,true,false]) ++ (L),([true]) ++ ([true,false,true,false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase14 (n : Nat) : run0 table (20*n) ⟨0,([true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true]) ++ (rep [true,false] (n))⟩ = some ⟨0,([true,false,true,false,true,false,true,false,true]),([true]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ (rep [true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,false,true,false,true,false,true,false] [true] [true,false,true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false,true,false] 20 local14 n (([true])) ((rep [true,false] (n)))

theorem phase15 (n : Nat) : run0 table 21 ⟨0,([true,false,true,false,true,false,true,false,true]),([true]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ (rep [true,false] (n))⟩ = some ⟨1,([true,true]),([true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ (rep [true,false] (n))⟩ := by rfl

theorem local16 (L R : List Bool) : run0 table 20 ⟨1,([true]) ++ (L),([true,false,true,false,true,false,true,false,true,false]) ++ ([true,false,true,false,true,false,true,false,true,false]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true,false,true,false,true,false,true,false]) ++ (L),([true,false,true,false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase16 (n : Nat) : run0 table (20*n) ⟨1,([true,true]),([true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ (rep [true,false] (n))⟩ = some ⟨1,([true]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,false,true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false,true,false] 20 local16 n (([true])) ((rep [true,false] (n)))

theorem local17 (L R : List Bool) : run0 table 4 ⟨1,([true]) ++ (L),([true,false,true,false,true,false,true,false,true,false]) ++ ([true,false]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false]) ++ (L),([true,false,true,false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase17 (n : Nat) : run0 table (4*n) ⟨1,([true]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨1,([true]) ++ (rep [true,false] (n)) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true,false,true,false,true,false,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,false,true,false,true,false,true,false,true,false] [true,false] [true,false] 4 local17 n ((rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) ([])

theorem phase18 (n : Nat) : run0 table 22 ⟨1,([true]) ++ (rep [true,false] (n)) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true,false,true,false,true,false,true,false,true,false])⟩ = some ⟨1,([false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false] (n)) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false] (n)) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]) = ([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)) := by
  calc
    _ = ([false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true] (n)) ++ ([false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,false,true,false,true,false,true,false,true])) ((rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) [true] false n
    _ = ([false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,false,true,false,true,false,true,false])) (([false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) [false] true n
    _ = ([false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true] (n)) ++ ([false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,false,true,false,true,false,true])) (([true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) [true] false n
    _ = ([false,true,false,true,false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,false,true,false,true,false])) (([false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) [false] true n
    _ = ([false,true,false,true,false,true,false,true]) ++ (rep [false,true] (n)) ++ ([false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,false,true,false,true])) (([true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) [true] false n
    _ = ([false,true,false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,false,true,false])) (([false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) [false] true n
    _ = ([false,true,false,true,false,true]) ++ (rep [false,true] (n)) ++ ([false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,false,true])) (([true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) [true] false n
    _ = ([false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,false])) (([false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) [false] true n
    _ = ([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true])) (([true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) [true] false n
    _ = ([false,true,false]) ++ (rep [true,false] (n)) ++ ([true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false])) (([false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) [false] true n
    _ = ([false,true]) ++ (rep [false,true] (n)) ++ ([false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) [true] false n
    _ = ([false]) ++ (rep [true,false] (n)) ++ ([true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) [false] true n
    _ = (rep [false,true] (n)) ++ ([false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) [true] false n
    _ = (rep [false,true] (n)) ++ ([false,true,false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ((rep [false,true] (n)) ++ ([false,true,false,true,false,true,false,true,false,true,false,true,false])) ([]) [false,true,false,true,false,true,false,true,false] true n
    _ = ([false]) ++ (rep [true,false] (n)) ++ ([true,false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n))) [true] false n
    _ = ([false,true]) ++ (rep [false,true] (n)) ++ ([false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n))) [false] true n
    _ = ([false,true,false]) ++ (rep [true,false] (n)) ++ ([true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n))) [true] false n
    _ = ([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false])) (([false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n))) [false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (95+132*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n)) (phase9 n)) (phase10 n)) (phase11 n)) (phase12 n)) (phase13 n)) (phase14 n)) (phase15 n)) (phase16 n)) (phase17 n)) (phase18 n))
  rw [finalL n] at H
  rw [show 16+2*n+10*n+5+20*n+4*n+5+4*n+20*n+13+20*n+4*n+13+4*n+20*n+21+20*n+4*n+22=95+132*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 95+132*n) entry (by intro n; omega) growth m hm

#print axioms never

end M10315

namespace M11133

-- 1RB0LF_1RC0LA_0RD0RB_1LD1RE_1LF1RE_---1LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false,true,true,false]) ++ (rep [true,true,true] (n)) ++ ([true,false]) ++ (rep [true] (n)) ++ ([true]),[]⟩

theorem entry : run0 table 19 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 16 ⟨4,([false,true,true,false]) ++ (rep [true,true,true] (n)) ++ ([true,false]) ++ (rep [true] (n)) ++ ([true]),[]⟩ = some ⟨5,([true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,false]) ++ (rep [true] (n)) ++ ([true]),([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨5,([true,true,true,true,true,true]) ++ ([true,true,true]) ++ (L),(R)⟩ = some ⟨5,([true,true,true,true,true,true]) ++ (L),([false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨5,([true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,false]) ++ (rep [true] (n)) ++ ([true]),([true])⟩ = some ⟨5,([true,true,true,true,true,true,true,false]) ++ (rep [true] (n)) ++ ([true]),(rep [false,false,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,true,true,true,true,true] [] [true,true,true] [false,false,true] 3 local1 n (([true,false]) ++ (rep [true] (n)) ++ ([true])) (([true]))

theorem phase2 (n : Nat) : run0 table 9 ⟨5,([true,true,true,true,true,true,true,false]) ++ (rep [true] (n)) ++ ([true]),(rep [false,false,true] (n)) ++ ([true])⟩ = some ⟨1,([false,false,true]) ++ (rep [true] (n)) ++ ([true]),([false,true,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 9 ⟨1,([false]) ++ (L),([false,true,false,false,true]) ++ ([false,false,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,true,true]) ++ (L),([false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (9*n) ⟨1,([false,false,true]) ++ (rep [true] (n)) ++ ([true]),([false,true,false,false,true]) ++ (rep [false,false,true] (n)) ++ ([true])⟩ = some ⟨1,([false]) ++ (rep [true,true,true] (n)) ++ ([false,true]) ++ (rep [true] (n)) ++ ([true]),([false,true,false,false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [false,true,false,false,true] [false,false,true] [true,true,true] 9 local3 n (([false,true]) ++ (rep [true] (n)) ++ ([true])) (([true]))

theorem phase4 (n : Nat) : run0 table 13 ⟨1,([false]) ++ (rep [true,true,true] (n)) ++ ([false,true]) ++ (rep [true] (n)) ++ ([true]),([false,true,false,false,true,true])⟩ = some ⟨4,([false,true,true,false,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false,true]) ++ (rep [true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,false,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false,true]) ++ (rep [true] (n)) ++ ([true]) = ([false,true,true,false,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,false,true]) ++ (rep [true] (n)) ++ ([true]) := by
  calc
    _ = ([false,true,true,false,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,false,true]) ++ (rep [true] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,true,true])) (([false,true]) ++ (rep [true] (n)) ++ ([true])) [true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (38+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalL n] at H
  rw [show 16+3*n+9+9*n+13=38+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 19 (fun n => 38+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M11133

namespace M13138

-- 1RB1LA_1RC0LC_0RD0LA_1LD1RE_1RF1RE_0LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,[],([true,true,true]) ++ (rep [true,true] (n)) ++ ([false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨0,[],([true,true,true]) ++ (rep [true,true] (n)) ++ ([false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ = some ⟨4,([true,true,false,true,true]),(rep [true,true] (n)) ++ ([false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨4,([true]) ++ (L),([true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true]) ++ (L),(R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨4,([true,true,false,true,true]),(rep [true,true] (n)) ++ ([false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ = some ⟨4,([true]) ++ (rep [true,true] (n)) ++ ([true,false,true,true]),([false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [] [true,true] [true,true] 2 local1 n (([true,false,true,true])) (([false,false]) ++ (rep [false,false] (n)) ++ ([false]))

theorem phase2 (n : Nat) : run0 table 5 ⟨4,([true]) ++ (rep [true,true] (n)) ++ ([true,false,true,true]),([false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ = some ⟨0,(rep [true,true] (n)) ++ ([true,false,true,true]),([false,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 2 ⟨0,([true,true]) ++ (L),(R)⟩ = some ⟨0,(L),([true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (2*n) ⟨0,(rep [true,true] (n)) ++ ([true,false,true,true]),([false,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ = some ⟨0,([true,false,true,true]),(rep [true,true] (n)) ++ ([false,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [] [] [true,true] [true,true] 2 local3 n (([true,false,true,true])) (([false,false,false]) ++ (rep [false,false] (n)) ++ ([false]))

theorem phase4 (n : Nat) : run0 table 23 ⟨0,([true,false,true,true]),(rep [true,true] (n)) ++ ([false,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ = some ⟨4,([true,true,true,true,true]),([true]) ++ (rep [true,true] (n)) ++ ([false,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 2 ⟨4,([true]) ++ (L),([true]) ++ ([true,true]) ++ (R)⟩ = some ⟨4,([true]) ++ ([true,true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (2*n) ⟨4,([true,true,true,true,true]),([true]) ++ (rep [true,true] (n)) ++ ([false,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ = some ⟨4,([true]) ++ (rep [true,true] (n)) ++ ([true,true,true,true]),([true,false,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [true] [true] [true,true] [true,true] 2 local5 n (([true,true,true,true])) (([false,false,false]) ++ (rep [false,false] (n)) ++ ([false]))

theorem phase6 (n : Nat) : run0 table 6 ⟨4,([true]) ++ (rep [true,true] (n)) ++ ([true,true,true,true]),([true,false,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ = some ⟨0,([true]) ++ (rep [true,true] (n)) ++ ([true,true,true,true]),([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 2 ⟨0,([true]) ++ ([true,true]) ++ (L),(R)⟩ = some ⟨0,([true]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (2*n) ⟨0,([true]) ++ (rep [true,true] (n)) ++ ([true,true,true,true]),([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ = some ⟨0,([true,true,true,true,true]),(rep [true,true] (n)) ++ ([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true] [] [true,true] [true,true] 2 local7 n (([true,true,true,true])) (([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false]))

theorem phase8 (n : Nat) : run0 table 5 ⟨0,([true,true,true,true,true]),(rep [true,true] (n)) ++ ([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ = some ⟨0,[],([true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false]) = ([true,true,true,true,true]) ++ (rep [true,true] (n)) ++ ([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([false]) := by
  rfl

theorem growth (n : Nat) : run0 table (46+8*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 7+2*n+5+2*n+23+2*n+6+2*n+5=46+8*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 15 (fun n => 46+8*n) entry (by intro n; omega) growth m hm

#print axioms never

end M13138

namespace M13439

-- 1RB0LF_1RC0RA_0RD---_1LD1RE_1RF1RE_1LA0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,true] (n)) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 22 ⟨1,([false,true]) ++ (rep [false,true] (n)) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)),[]⟩ = some ⟨4,([false,true]) ++ (rep [false,true] (n)) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)),([false,true,true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨4,([false,true]) ++ ([false,true]) ++ (L),([false]) ++ (R)⟩ = some ⟨4,([false,true]) ++ (L),([false]) ++ ([false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨4,([false,true]) ++ (rep [false,true] (n)) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)),([false,true,true,true])⟩ = some ⟨4,([false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)),([false]) ++ (rep [false,true] (n)) ++ ([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true] [false] [false,true] [false,true] 4 local1 n ((rep [false,true,false,true,false,true,false,true,false,true] (n))) (([true,true,true]))

theorem local2 (L R : List Bool) : run0 table 20 ⟨4,([false,true]) ++ ([false,true,false,true,false,true,false,true,false,true]) ++ (L),([false]) ++ (R)⟩ = some ⟨4,([false,true]) ++ (L),([false]) ++ ([false,true,false,true,false,true,false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (20*n) ⟨4,([false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)),([false]) ++ (rep [false,true] (n)) ++ ([true,true,true])⟩ = some ⟨4,([false,true]),([false]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)) ++ (rep [false,true] (n)) ++ ([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true] [false] [false,true,false,true,false,true,false,true,false,true] [false,true,false,true,false,true,false,true,false,true] 20 local2 n ([]) ((rep [false,true] (n)) ++ ([true,true,true]))

theorem phase3 (n : Nat) : run0 table 9 ⟨4,([false,true]),([false]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)) ++ (rep [false,true] (n)) ++ ([true,true,true])⟩ = some ⟨1,([true,true]),([false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)) ++ (rep [false,true] (n)) ++ ([true,true,true])⟩ := by rfl

theorem local4 (L R : List Bool) : run0 table 10 ⟨1,([true]) ++ (L),([false,true,false,true]) ++ ([false,true,false,true,false,true,false,true,false,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true,false,true,false,true,false,true,false]) ++ (L),([false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase4 (n : Nat) : run0 table (10*n) ⟨1,([true,true]),([false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)) ++ (rep [false,true] (n)) ++ ([true,true,true])⟩ = some ⟨1,([true]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,true,false,true] [false,true,false,true,false,true,false,true,false,true] [true,false,true,false,true,false,true,false,true,false] 10 local4 n (([true])) ((rep [false,true] (n)) ++ ([true,true,true]))

theorem local5 (L R : List Bool) : run0 table 2 ⟨1,([true]) ++ (L),([false,true,false,true]) ++ ([false,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false]) ++ (L),([false,true,false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (2*n) ⟨1,([true]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([true,true,true])⟩ = some ⟨1,([true]) ++ (rep [true,false] (n)) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,true,false,true] [false,true] [true,false] 2 local5 n ((rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) (([true,true,true]))

theorem phase6 (n : Nat) : run0 table 5 ⟨1,([true]) ++ (rep [true,false] (n)) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true,true,true,true])⟩ = some ⟨0,([true,false,true,false,true,false]) ++ (rep [true,false] (n)) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true,true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 2 ⟨0,([true,false,true,false,true,false]) ++ ([true,false]) ++ (L),(R)⟩ = some ⟨0,([true,false,true,false,true,false]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (2*n) ⟨0,([true,false,true,false,true,false]) ++ (rep [true,false] (n)) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([true,true])⟩ = some ⟨0,([true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),(rep [true,false] (n)) ++ ([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,false,true,false,true,false] [] [true,false] [true,false] 2 local7 n ((rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) (([true,true]))

theorem local8 (L R : List Bool) : run0 table 10 ⟨0,([true,false,true,false,true,false]) ++ ([true,false,true,false,true,false,true,false,true,false]) ++ (L),(R)⟩ = some ⟨0,([true,false,true,false,true,false]) ++ (L),([true,false,true,false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase8 (n : Nat) : run0 table (10*n) ⟨0,([true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),(rep [true,false] (n)) ++ ([true,true])⟩ = some ⟨0,([true,false,true,false,true,false,true]),(rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ (rep [true,false] (n)) ++ ([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,false,true,false,true,false] [] [true,false,true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false,true,false] 10 local8 n (([true])) ((rep [true,false] (n)) ++ ([true,true]))

theorem phase9 (n : Nat) : run0 table 9 ⟨0,([true,false,true,false,true,false,true]),(rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ (rep [true,false] (n)) ++ ([true,true])⟩ = some ⟨1,([true,true]),([false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ (rep [true,false] (n)) ++ ([true,true])⟩ := by rfl

theorem local10 (L R : List Bool) : run0 table 10 ⟨1,([true]) ++ (L),([false,true,false,true,false,true,false]) ++ ([true,false,true,false,true,false,true,false,true,false]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true,false,true,false,true,false,true,false]) ++ (L),([false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase10 (n : Nat) : run0 table (10*n) ⟨1,([true,true]),([false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ (rep [true,false] (n)) ++ ([true,true])⟩ = some ⟨1,([true]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false,true,false] 10 local10 n (([true])) ((rep [true,false] (n)) ++ ([true,true]))

theorem local11 (L R : List Bool) : run0 table 2 ⟨1,([true]) ++ (L),([false,true,false,true,false,true,false]) ++ ([true,false]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false]) ++ (L),([false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase11 (n : Nat) : run0 table (2*n) ⟨1,([true]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true,true])⟩ = some ⟨1,([true]) ++ (rep [true,false] (n)) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,true,false,true,false,true,false] [true,false] [true,false] 2 local11 n ((rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) (([true,true]))

theorem phase12 (n : Nat) : run0 table 9 ⟨1,([true]) ++ (rep [true,false] (n)) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,true,true])⟩ = some ⟨0,([true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false] (n)) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem local13 (L R : List Bool) : run0 table 2 ⟨0,([true,false,true,false,true,false,true,false,true,false]) ++ ([true,false]) ++ (L),(R)⟩ = some ⟨0,([true,false,true,false,true,false,true,false,true,false]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase13 (n : Nat) : run0 table (2*n) ⟨0,([true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false] (n)) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),[]⟩ = some ⟨0,([true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),(rep [true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,false,true,false,true,false,true,false,true,false] [] [true,false] [true,false] 2 local13 n ((rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) ([])

theorem local14 (L R : List Bool) : run0 table 10 ⟨0,([true,false,true,false,true,false,true,false,true,false]) ++ ([true,false,true,false,true,false,true,false,true,false]) ++ (L),(R)⟩ = some ⟨0,([true,false,true,false,true,false,true,false,true,false]) ++ (L),([true,false,true,false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase14 (n : Nat) : run0 table (10*n) ⟨0,([true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),(rep [true,false] (n))⟩ = some ⟨0,([true,false,true,false,true,false,true,false,true,false,true]),(rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ (rep [true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,false,true,false,true,false,true,false,true,false] [] [true,false,true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false,true,false] 10 local14 n (([true])) ((rep [true,false] (n)))

theorem phase15 (n : Nat) : run0 table 13 ⟨0,([true,false,true,false,true,false,true,false,true,false,true]),(rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ (rep [true,false] (n))⟩ = some ⟨1,([true,true]),([false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ (rep [true,false] (n))⟩ := by rfl

theorem local16 (L R : List Bool) : run0 table 10 ⟨1,([true]) ++ (L),([false,true,false,true,false,true,false,true,false,true,false]) ++ ([true,false,true,false,true,false,true,false,true,false]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true,false,true,false,true,false,true,false]) ++ (L),([false,true,false,true,false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase16 (n : Nat) : run0 table (10*n) ⟨1,([true,true]),([false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ (rep [true,false] (n))⟩ = some ⟨1,([true]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,true,false,true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false,true,false] 10 local16 n (([true])) ((rep [true,false] (n)))

theorem local17 (L R : List Bool) : run0 table 2 ⟨1,([true]) ++ (L),([false,true,false,true,false,true,false,true,false,true,false]) ++ ([true,false]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false]) ++ (L),([false,true,false,true,false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase17 (n : Nat) : run0 table (2*n) ⟨1,([true]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false] (n))⟩ = some ⟨1,([true]) ++ (rep [true,false] (n)) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,true,false,true,false,true,false,true,false,true,false] [true,false] [true,false] 2 local17 n ((rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) ([])

theorem phase18 (n : Nat) : run0 table 12 ⟨1,([true]) ++ (rep [true,false] (n)) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),([false,true,false,true,false,true,false,true,false,true,false])⟩ = some ⟨1,([false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false] (n)) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false] (n)) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]) = ([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)) := by
  calc
    _ = ([false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true] (n)) ++ ([false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,false,true,false,true,false,true,false,true])) ((rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) [true] false n
    _ = ([false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,false,true,false,true,false,true,false])) (([false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) [false] true n
    _ = ([false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true] (n)) ++ ([false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,false,true,false,true,false,true])) (([true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) [true] false n
    _ = ([false,true,false,true,false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,false,true,false,true,false])) (([false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) [false] true n
    _ = ([false,true,false,true,false,true,false,true]) ++ (rep [false,true] (n)) ++ ([false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,false,true,false,true])) (([true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) [true] false n
    _ = ([false,true,false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,false,true,false])) (([false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) [false] true n
    _ = ([false,true,false,true,false,true]) ++ (rep [false,true] (n)) ++ ([false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,false,true])) (([true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) [true] false n
    _ = ([false,true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true,false])) (([false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) [false] true n
    _ = ([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,true])) (([true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) [true] false n
    _ = ([false,true,false]) ++ (rep [true,false] (n)) ++ ([true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false])) (([false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) [false] true n
    _ = ([false,true]) ++ (rep [false,true] (n)) ++ ([false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) [true] false n
    _ = ([false]) ++ (rep [true,false] (n)) ++ ([true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) [false] true n
    _ = (rep [false,true] (n)) ++ ([false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false] (n)) ++ ([true])) [true] false n
    _ = (rep [false,true] (n)) ++ ([false,true,false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ((rep [false,true] (n)) ++ ([false,true,false,true,false,true,false,true,false,true,false,true,false])) ([]) [false,true,false,true,false,true,false,true,false] true n
    _ = ([false]) ++ (rep [true,false] (n)) ++ ([true,false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n))) [true] false n
    _ = ([false,true]) ++ (rep [false,true] (n)) ++ ([false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n))) [false] true n
    _ = ([false,true,false]) ++ (rep [true,false] (n)) ++ ([true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([true,false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n))) [true] false n
    _ = ([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false])) (([false,true,false,true,false,true,false,true,false,true]) ++ (rep [false,true,false,true,false,true,false,true,false,true] (n))) [false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (79+84*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n)) (phase9 n)) (phase10 n)) (phase11 n)) (phase12 n)) (phase13 n)) (phase14 n)) (phase15 n)) (phase16 n)) (phase17 n)) (phase18 n))
  rw [finalL n] at H
  rw [show 22+4*n+20*n+9+10*n+2*n+5+2*n+10*n+9+10*n+2*n+9+2*n+10*n+13+10*n+2*n+12=79+84*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 79+84*n) entry (by intro n; omega) growth m hm

#print axioms never

end M13439

namespace M4050

-- 1RB---_1RC0LF_0RD1RB_1LD1RE_0RF1RE_1LA1LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),[]⟩

theorem entry : run0 table 108 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 3 ⟨4,([false]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),[]⟩ = some ⟨1,([true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),[]⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 16 ⟨1,([true,true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨1,([true,true]) ++ (L),([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (16*n) ⟨1,([true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),[]⟩ = some ⟨1,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),(rep [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true] [] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] 16 local1 n (([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true])) ([])

theorem phase2 (n : Nat) : run0 table 23 ⟨1,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),(rep [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] (n))⟩ = some ⟨2,([true,true]),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] (n))⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 16 ⟨2,([true]) ++ (L),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ ([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (16*n) ⟨2,([true,true]),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] (n))⟩ = some ⟨2,([true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] 16 local3 n (([true])) ([])

theorem phase4 (n : Nat) : run0 table 31 ⟨2,([true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),([false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false])⟩ = some ⟨1,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 16 ⟨1,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨1,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (16*n) ⟨1,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true]),[]⟩ = some ⟨1,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),(rep [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] 16 local5 n (([true])) ([])

theorem phase6 (n : Nat) : run0 table 38 ⟨1,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]),(rep [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] (n))⟩ = some ⟨1,([false,true,false,true,true,true]),([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] (n))⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 16 ⟨1,([false]) ++ (L),([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ ([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (16*n) ⟨1,([false,true,false,true,true,true]),([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] (n))⟩ = some ⟨1,([false]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true,false,true,true,true]),([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] 16 local7 n (([true,false,true,true,true])) ([])

theorem phase8 (n : Nat) : run0 table 34 ⟨1,([false]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true,false,true,true,true]),([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false])⟩ = some ⟨1,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true,false,true,true,true]),[]⟩ := by rfl

theorem local9 (L R : List Bool) : run0 table 16 ⟨1,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨1,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase9 (n : Nat) : run0 table (16*n) ⟨1,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true,false,true,true,true]),[]⟩ = some ⟨1,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true]),(rep [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] 16 local9 n (([true,false,true,true,true])) ([])

theorem phase10 (n : Nat) : run0 table 30 ⟨1,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true]),(rep [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] (n))⟩ = some ⟨1,([false,true,true,true]),([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] (n))⟩ := by rfl

theorem local11 (L R : List Bool) : run0 table 16 ⟨1,([false]) ++ (L),([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ ([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase11 (n : Nat) : run0 table (16*n) ⟨1,([false,true,true,true]),([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) ++ (rep [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] (n))⟩ = some ⟨1,([false]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true]),([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] 16 local11 n (([true,true,true])) ([])

theorem phase12 (n : Nat) : run0 table 37 ⟨1,([false]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true]),([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false])⟩ = some ⟨4,([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true]) = ([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) := by
  calc
    _ = ([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true])) (([true,true,true])) [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] true n
    _ = ([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true])) (([true,true,true,true])) [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] true n
    _ = ([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true])) (([true,true,true,true,true])) [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] true n
    _ = ([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true])) (([true,true,true,true,true,true])) [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] true n
    _ = ([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true])) (([true,true,true,true,true,true,true])) [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] true n
    _ = ([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true])) (([true,true,true,true,true,true,true,true])) [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] true n
    _ = ([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true])) (([true,true,true,true,true,true,true,true,true])) [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] true n
    _ = ([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true])) (([true,true,true,true,true,true,true,true,true,true])) [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] true n
    _ = ([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true,true,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true])) (([true,true,true,true,true,true,true,true,true,true,true])) [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] true n
    _ = ([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true])) (([true,true,true,true,true,true,true,true,true,true,true,true])) [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] true n
    _ = ([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true])) (([true,true,true,true,true,true,true,true,true,true,true,true,true])) [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] true n
    _ = ([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true])) (([true,true,true,true,true,true,true,true,true,true,true,true,true,true])) [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] true n
    _ = ([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true])) (([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true])) [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] true n
    _ = ([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true])) (([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true])) [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] true n
    _ = ([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true])) (([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true])) [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] true n
    _ = ([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true])) (([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true])) [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] true n
    _ = ([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true])) (([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true])) [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (196+96*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n)) (phase9 n)) (phase10 n)) (phase11 n)) (phase12 n))
  rw [finalL n] at H
  rw [show 3+16*n+23+16*n+31+16*n+38+16*n+34+16*n+30+16*n+37=196+96*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 108 (fun n => 196+96*n) entry (by intro n; omega) growth m hm

#print axioms never

end M4050

namespace M4669

-- 1RB0LE_1RC1RF_0RD---_1LD1RE_1LA1RE_0RB0RA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨false,true,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false,true,true]) ++ (rep [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] (n)) ++ ([true,false,true,false,true,true,false,true,false,true,true]),[]⟩

theorem entry : run0 table 51 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 3 ⟨4,([false,true,true]) ++ (rep [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] (n)) ++ ([true,false,true,false,true,true,false,true,false,true,true]),[]⟩ = some ⟨4,([false,true]) ++ (rep [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] (n)) ++ ([true,false,true,false,true,true,false,true,false,true,true]),([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 35 ⟨4,([false,true]) ++ ([true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (L),(R)⟩ = some ⟨4,([false,true]) ++ (L),([false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (35*n) ⟨4,([false,true]) ++ (rep [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] (n)) ++ ([true,false,true,false,true,true,false,true,false,true,true]),([true])⟩ = some ⟨4,([false,true,true,false,true,false,true,true,false,true,false,true,true]),(rep [false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true] [] [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] [false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true] 35 local1 n (([true,false,true,false,true,true,false,true,false,true,true])) (([true]))

theorem phase2 (n : Nat) : run0 table 21 ⟨4,([false,true,true,false,true,false,true,true,false,true,false,true,true]),(rep [false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true] (n)) ++ ([true])⟩ = some ⟨1,([true,true]),([false,true,true,false,true,false,true,true,false,true,false,true,true]) ++ (rep [false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true] (n)) ++ ([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 25 ⟨1,([true]) ++ (L),([false,true,true,false,true,false,true,true,false,true,false,true,true]) ++ ([false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (L),([false,true,true,false,true,false,true,true,false,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (25*n) ⟨1,([true,true]),([false,true,true,false,true,false,true,true,false,true,false,true,true]) ++ (rep [false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true] (n)) ++ ([true])⟩ = some ⟨1,([true]) ++ (rep [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] (n)) ++ ([true]),([false,true,true,false,true,false,true,true,false,true,false,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,true,true,false,true,false,true,true,false,true,false,true,true] [false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true] [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] 25 local3 n (([true])) (([true]))

theorem phase4 (n : Nat) : run0 table 14 ⟨1,([true]) ++ (rep [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] (n)) ++ ([true]),([false,true,true,false,true,false,true,true,false,true,false,true,true,true])⟩ = some ⟨0,([true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (rep [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 35 ⟨0,([true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ ([true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (L),(R)⟩ = some ⟨0,([true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (L),([true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (35*n) ⟨0,([true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (rep [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] (n)) ++ ([true]),[]⟩ = some ⟨0,([true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true]),(rep [true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] [] [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] [true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false] 35 local5 n (([true])) ([])

theorem phase6 (n : Nat) : run0 table 24 ⟨0,([true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true]),(rep [true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false] (n))⟩ = some ⟨1,([true,true]),([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false]) ++ (rep [true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false] (n))⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 25 ⟨1,([true]) ++ (L),([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false]) ++ ([true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (L),([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (25*n) ⟨1,([true,true]),([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false]) ++ (rep [true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false] (n))⟩ = some ⟨1,([true]) ++ (rep [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] (n)) ++ ([true]),([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false] [true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false] [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] 25 local7 n (([true])) ([])

theorem phase8 (n : Nat) : run0 table 30 ⟨1,([true]) ++ (rep [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] (n)) ++ ([true]),([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false])⟩ = some ⟨4,([false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (rep [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] (n)) ++ ([true]),([true,true])⟩ := by rfl

theorem local9 (L R : List Bool) : run0 table 35 ⟨4,([false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ ([true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (L),([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase9 (n : Nat) : run0 table (35*n) ⟨4,([false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (rep [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] (n)) ++ ([true]),([true,true])⟩ = some ⟨4,([false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true]),(rep [false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true] (n)) ++ ([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] [] [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] [false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true] 35 local9 n (([true])) (([true,true]))

theorem phase10 (n : Nat) : run0 table 30 ⟨4,([false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true]),(rep [false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true] (n)) ++ ([true,true])⟩ = some ⟨1,([true,true]),([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true]) ++ (rep [false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true] (n)) ++ ([true,true])⟩ := by rfl

theorem local11 (L R : List Bool) : run0 table 25 ⟨1,([true]) ++ (L),([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true]) ++ ([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (L),([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase11 (n : Nat) : run0 table (25*n) ⟨1,([true,true]),([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true]) ++ (rep [false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true] (n)) ++ ([true,true])⟩ = some ⟨1,([true]) ++ (rep [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] (n)) ++ ([true]),([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true] [false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true] [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] 25 local11 n (([true])) (([true,true]))

theorem phase12 (n : Nat) : run0 table 22 ⟨1,([true]) ++ (rep [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] (n)) ++ ([true]),([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,true,true])⟩ = some ⟨0,([true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (rep [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem local13 (L R : List Bool) : run0 table 35 ⟨0,([true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ ([true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (L),(R)⟩ = some ⟨0,([true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (L),([true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase13 (n : Nat) : run0 table (35*n) ⟨0,([true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (rep [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] (n)) ++ ([true]),[]⟩ = some ⟨0,([true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true]),(rep [true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] [] [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] [true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false] 35 local13 n (([true])) ([])

theorem phase14 (n : Nat) : run0 table 36 ⟨0,([true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true]),(rep [true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false] (n))⟩ = some ⟨1,([true,true]),([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false]) ++ (rep [true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false] (n))⟩ := by rfl

theorem local15 (L R : List Bool) : run0 table 25 ⟨1,([true]) ++ (L),([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false]) ++ ([true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (L),([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase15 (n : Nat) : run0 table (25*n) ⟨1,([true,true]),([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false]) ++ (rep [true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false] (n))⟩ = some ⟨1,([true]) ++ (rep [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] (n)) ++ ([true]),([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false] [true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false] [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] 25 local15 n (([true])) ([])

theorem phase16 (n : Nat) : run0 table 38 ⟨1,([true]) ++ (rep [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] (n)) ++ ([true]),([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false])⟩ = some ⟨4,([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (rep [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] (n)) ++ ([true]),([true,true])⟩ := by rfl

theorem local17 (L R : List Bool) : run0 table 35 ⟨4,([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ ([true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (L),([false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase17 (n : Nat) : run0 table (35*n) ⟨4,([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (rep [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] (n)) ++ ([true]),([true,true])⟩ = some ⟨4,([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true]),(rep [false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true] (n)) ++ ([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] [] [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] [false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true] 35 local17 n (([true])) (([true,true]))

theorem phase18 (n : Nat) : run0 table 42 ⟨4,([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true]),(rep [false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true] (n)) ++ ([true,true])⟩ = some ⟨1,([true,true]),([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true]) ++ (rep [false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true] (n)) ++ ([true,true])⟩ := by rfl

theorem local19 (L R : List Bool) : run0 table 25 ⟨1,([true]) ++ (L),([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true]) ++ ([false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (L),([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase19 (n : Nat) : run0 table (25*n) ⟨1,([true,true]),([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true]) ++ (rep [false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true] (n)) ++ ([true,true])⟩ = some ⟨1,([true]) ++ (rep [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] (n)) ++ ([true]),([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true] [false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true] [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] 25 local19 n (([true])) (([true,true]))

theorem phase20 (n : Nat) : run0 table 29 ⟨1,([true]) ++ (rep [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] (n)) ++ ([true]),([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,true,true])⟩ = some ⟨0,([true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (rep [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] (n)) ++ ([true]),([true])⟩ := by rfl

theorem local21 (L R : List Bool) : run0 table 35 ⟨0,([true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ ([true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (L),(R)⟩ = some ⟨0,([true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (L),([true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase21 (n : Nat) : run0 table (35*n) ⟨0,([true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (rep [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] (n)) ++ ([true]),([true])⟩ = some ⟨0,([true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true]),(rep [true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 0 [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] [] [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] [true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false] 35 local21 n (([true])) (([true]))

theorem phase22 (n : Nat) : run0 table 45 ⟨0,([true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true]),(rep [true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false] (n)) ++ ([true])⟩ = some ⟨1,([true,true]),([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false]) ++ (rep [true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false] (n)) ++ ([true])⟩ := by rfl

theorem local23 (L R : List Bool) : run0 table 25 ⟨1,([true]) ++ (L),([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false]) ++ ([true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (L),([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase23 (n : Nat) : run0 table (25*n) ⟨1,([true,true]),([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false]) ++ (rep [true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false] (n)) ++ ([true])⟩ = some ⟨1,([true]) ++ (rep [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] (n)) ++ ([true]),([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false] [true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false] [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] 25 local23 n (([true])) (([true]))

theorem phase24 (n : Nat) : run0 table 41 ⟨1,([true]) ++ (rep [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] (n)) ++ ([true]),([false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true])⟩ = some ⟨4,([false,true,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (rep [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (rep [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] (n)) ++ ([true]) = ([false,true,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (rep [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] (n)) ++ ([true,false,true,false,true,true,false,true,false,true,true]) := by
  calc
    _ = ([false,true,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false]) ++ (rep [true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false] (n)) ++ ([true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false])) (([true])) [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false] true n
    _ = ([false,true,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true]) ++ (rep [false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true] (n)) ++ ([false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true])) (([true,true])) [true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true] false n
    _ = ([false,true,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false]) ++ (rep [true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false] (n)) ++ ([true,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false])) (([false,true,true])) [false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false] true n
    _ = ([false,true,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true]) ++ (rep [false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true] (n)) ++ ([false,true,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true])) (([true,false,true,true])) [true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true] false n
    _ = ([false,true,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (rep [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] (n)) ++ ([true,false,true,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true])) (([false,true,false,true,true])) [false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] true n
    _ = ([false,true,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false]) ++ (rep [true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false] (n)) ++ ([true,true,false,true,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false])) (([true,false,true,false,true,true])) [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false] true n
    _ = ([false,true,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true]) ++ (rep [false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true] (n)) ++ ([false,true,true,false,true,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true])) (([true,true,false,true,false,true,true])) [true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true] false n
    _ = ([false,true,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false]) ++ (rep [true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false] (n)) ++ ([true,false,true,true,false,true,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false])) (([false,true,true,false,true,false,true,true])) [false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false] true n
    _ = ([false,true,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true]) ++ (rep [false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true] (n)) ++ ([false,true,false,true,true,false,true,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true])) (([true,false,true,true,false,true,false,true,true])) [true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true] false n
    _ = ([false,true,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true]) ++ (rep [true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] (n)) ++ ([true,false,true,false,true,true,false,true,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true])) (([false,true,false,true,true,false,true,false,true,true])) [false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true,true,false,true,false,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (375+360*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n)) (phase9 n)) (phase10 n)) (phase11 n)) (phase12 n)) (phase13 n)) (phase14 n)) (phase15 n)) (phase16 n)) (phase17 n)) (phase18 n)) (phase19 n)) (phase20 n)) (phase21 n)) (phase22 n)) (phase23 n)) (phase24 n))
  rw [finalL n] at H
  rw [show 3+35*n+21+25*n+14+35*n+24+25*n+30+35*n+30+25*n+22+35*n+36+25*n+38+35*n+42+25*n+29+35*n+45+25*n+41=375+360*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 51 (fun n => 375+360*n) entry (by intro n; omega) growth m hm

#print axioms never

end M4669

namespace M7065

-- 1RB---_1RC0LF_0RD0RA_1LD1RE_1LB1RE_0RF0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false,true,true,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true,false,true,true,true,false,true]),[]⟩

theorem entry : run0 table 55 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 4 ⟨4,([false,true,true,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true,false,true,true,true,false,true]),[]⟩ = some ⟨4,([false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true,false,true,true,true,false,true]),([false,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 15 ⟨4,([false,true]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),(R)⟩ = some ⟨4,([false,true]) ++ (L),([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (15*n) ⟨4,([false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true,false,true,true,true,false,true]),([false,true])⟩ = some ⟨4,([false,true,true,false,true,true,true,false,true]),(rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true] [] [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] 15 local1 n (([true,false,true,true,true,false,true])) (([false,true]))

theorem phase2 (n : Nat) : run0 table 13 ⟨4,([false,true,true,false,true,true,true,false,true]),(rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([false,true])⟩ = some ⟨1,([false,true]),([true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([false,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 15 ⟨1,([false]) ++ (L),([true,false,false,true,false,false,true]) ++ ([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),([true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (15*n) ⟨1,([false,true]),([true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([false,true])⟩ = some ⟨1,([false]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([true,false,false,true,false,false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,false,false,true,false,false,true] [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] 15 local3 n (([true])) (([false,true]))

theorem phase4 (n : Nat) : run0 table 9 ⟨1,([false]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([true,false,false,true,false,false,true,false,true])⟩ = some ⟨1,([true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 15 ⟨1,([true,true,false,true,true,false,true,true,false,true]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,true,true,false,true,true,false,true]) ++ (L),([true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (15*n) ⟨1,([true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),[]⟩ = some ⟨1,([true,true,false,true,true,false,true,true,false,true,true]),(rep [true,false,false,true,false,false,true,false,false,true,false,false,true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,true,true,false,true,true,false,true] [] [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] [true,false,false,true,false,false,true,false,false,true,false,false,true,false,false] 15 local5 n (([true])) ([])

theorem phase6 (n : Nat) : run0 table 13 ⟨1,([true,true,false,true,true,false,true,true,false,true,true]),(rep [true,false,false,true,false,false,true,false,false,true,false,false,true,false,false] (n))⟩ = some ⟨2,([true,true]),([false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false,true,false,false,true,false,false] (n))⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 15 ⟨2,([true]) ++ (L),([false,false,true,false,false,true,false,false,true,false,false]) ++ ([true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (L),([false,false,true,false,false,true,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (15*n) ⟨2,([true,true]),([false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false,true,false,false,true,false,false] (n))⟩ = some ⟨2,([true]) ++ (rep [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] (n)) ++ ([true]),([false,false,true,false,false,true,false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,false,true,false,false,true,false,false,true,false,false] [true,false,false,true,false,false,true,false,false,true,false,false,true,false,false] [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] 15 local7 n (([true])) ([])

theorem phase8 (n : Nat) : run0 table 22 ⟨2,([true]) ++ (rep [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] (n)) ++ ([true]),([false,false,true,false,false,true,false,false,true,false,false])⟩ = some ⟨4,([false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] (n)) ++ ([true]),([false,true])⟩ := by rfl

theorem local9 (L R : List Bool) : run0 table 15 ⟨4,([false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ ([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (L),(R)⟩ = some ⟨4,([false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (L),([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase9 (n : Nat) : run0 table (15*n) ⟨4,([false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] (n)) ++ ([true]),([false,true])⟩ = some ⟨4,([false,true,true,false,true,true,false,true,true,false,true,true,false,true]),(rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true,false,true,true,false,true,true,false,true,true,false] [] [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] 15 local9 n (([true])) (([false,true]))

theorem phase10 (n : Nat) : run0 table 30 ⟨4,([false,true,true,false,true,true,false,true,true,false,true,true,false,true]),(rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([false,true])⟩ = some ⟨1,([false,true,true,false,true]),([true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([false,true])⟩ := by rfl

theorem local11 (L R : List Bool) : run0 table 15 ⟨1,([false]) ++ (L),([true,false,false,true,false,false,true,false,false,true]) ++ ([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),([true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase11 (n : Nat) : run0 table (15*n) ⟨1,([false,true,true,false,true]),([true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([false,true])⟩ = some ⟨1,([false]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true,true,false,true]),([true,false,false,true,false,false,true,false,false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,false,false,true,false,false,true,false,false,true] [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] 15 local11 n (([true,true,false,true])) (([false,true]))

theorem phase12 (n : Nat) : run0 table 12 ⟨1,([false]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true,true,false,true]),([true,false,false,true,false,false,true,false,false,true,false,true])⟩ = some ⟨1,([true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true,true,false,true]),[]⟩ := by rfl

theorem local13 (L R : List Bool) : run0 table 15 ⟨1,([true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),([true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase13 (n : Nat) : run0 table (15*n) ⟨1,([true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true,true,false,true]),[]⟩ = some ⟨1,([true,true,false,true,true,false,true,true,false,true,true,false,true,true,true,false,true]),(rep [true,false,false,true,false,false,true,false,false,true,false,false,true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,true,true,false,true,true,false,true,true,false,true] [] [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] [true,false,false,true,false,false,true,false,false,true,false,false,true,false,false] 15 local13 n (([true,true,false,true])) ([])

theorem phase14 (n : Nat) : run0 table 21 ⟨1,([true,true,false,true,true,false,true,true,false,true,true,false,true,true,true,false,true]),(rep [true,false,false,true,false,false,true,false,false,true,false,false,true,false,false] (n))⟩ = some ⟨1,([false,true]),([true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false,true,false,false,true,false,false] (n))⟩ := by rfl

theorem local15 (L R : List Bool) : run0 table 15 ⟨1,([false]) ++ (L),([true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ ([true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),([true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase15 (n : Nat) : run0 table (15*n) ⟨1,([false,true]),([true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false,true,false,false,true,false,false] (n))⟩ = some ⟨1,([false]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([true,false,false,true,false,false,true,false,false,true,false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,false,false,true,false,false,true,false,false,true,false,false,true,false,false] [true,false,false,true,false,false,true,false,false,true,false,false,true,false,false] [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] 15 local15 n (([true])) ([])

theorem phase16 (n : Nat) : run0 table 26 ⟨1,([false]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([true,false,false,true,false,false,true,false,false,true,false,false,true,false,false])⟩ = some ⟨4,([false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([false,true])⟩ := by rfl

theorem local17 (L R : List Bool) : run0 table 15 ⟨4,([false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase17 (n : Nat) : run0 table (15*n) ⟨4,([false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([false,true])⟩ = some ⟨4,([false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]),(rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] [] [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] 15 local17 n (([true])) (([false,true]))

theorem phase18 (n : Nat) : run0 table 20 ⟨4,([false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]),(rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([false,true])⟩ = some ⟨2,([true,true]),([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([false,true])⟩ := by rfl

theorem local19 (L R : List Bool) : run0 table 15 ⟨2,([true]) ++ (L),([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ ([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (L),([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase19 (n : Nat) : run0 table (15*n) ⟨2,([true,true]),([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([false,true])⟩ = some ⟨2,([true]) ++ (rep [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] (n)) ++ ([true]),([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] 15 local19 n (([true])) (([false,true]))

theorem phase20 (n : Nat) : run0 table 20 ⟨2,([true]) ++ (rep [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] (n)) ++ ([true]),([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,true])⟩ = some ⟨1,([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem local21 (L R : List Bool) : run0 table 15 ⟨1,([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ ([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (L),([true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase21 (n : Nat) : run0 table (15*n) ⟨1,([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] (n)) ++ ([true]),[]⟩ = some ⟨1,([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]),(rep [true,false,false,true,false,false,true,false,false,true,false,false,true,false,false] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] [] [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] [true,false,false,true,false,false,true,false,false,true,false,false,true,false,false] 15 local21 n (([true])) ([])

theorem phase22 (n : Nat) : run0 table 38 ⟨1,([true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]),(rep [true,false,false,true,false,false,true,false,false,true,false,false,true,false,false] (n))⟩ = some ⟨1,([false,true,true,false,true]),([true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false,true,false,false,true,false,false] (n))⟩ := by rfl

theorem local23 (L R : List Bool) : run0 table 15 ⟨1,([false]) ++ (L),([true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ ([true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),([true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (R)⟩ := by rfl

theorem phase23 (n : Nat) : run0 table (15*n) ⟨1,([false,true,true,false,true]),([true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false,true,false,false,true,false,false] (n))⟩ = some ⟨1,([false]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true,true,false,true]),([true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false] [true,false,false,true,false,false,true,false,false,true,false,false,true,false,false] [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] 15 local23 n (([true,true,false,true])) ([])

theorem phase24 (n : Nat) : run0 table 25 ⟨1,([false]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true,true,false,true]),([true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false])⟩ = some ⟨4,([false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true,true,false,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true,true,false,true]) = ([false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true,false,true,true,true,false,true]) := by
  calc
    _ = ([false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] (n)) ++ ([true,true,true,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false])) (([true,true,false,true])) [true,false,true,true,false,true,true,false,true,true,false,true,true,false] true n
    _ = ([false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,true,true,true,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true])) (([true,true,true,false,true])) [true,true,false,true,true,false,true,true,false,true,true,false,true,true] false n
    _ = ([false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true,false,true,true,true,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true])) (([false,true,true,true,false,true])) [false,true,true,false,true,true,false,true,true,false,true,true,false,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (253+180*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n)) (phase9 n)) (phase10 n)) (phase11 n)) (phase12 n)) (phase13 n)) (phase14 n)) (phase15 n)) (phase16 n)) (phase17 n)) (phase18 n)) (phase19 n)) (phase20 n)) (phase21 n)) (phase22 n)) (phase23 n)) (phase24 n))
  rw [finalL n] at H
  rw [show 4+15*n+13+15*n+9+15*n+13+15*n+22+15*n+30+15*n+12+15*n+21+15*n+26+15*n+20+15*n+20+15*n+38+15*n+25=253+180*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 55 (fun n => 253+180*n) entry (by intro n; omega) growth m hm

#print axioms never

end M7065

namespace M9673

-- 1RB0LE_1RC---_0RD0RC_1LD1RE_1LF1RE_0LB0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,([false,true,false,false]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true,true,false,true,true]),[]⟩

theorem entry : run0 table 80 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 52 ⟨4,([false,true,false,false]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true,true,false,true,true]),[]⟩ = some ⟨4,([false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true,true,false,true,true]),([false,true,false,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 18 ⟨4,([false,true,true,false,true,true]) ++ ([false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true,false,true,true]) ++ (L),([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (18*n) ⟨4,([false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true,true,false,true,true]),([false,true,false,true])⟩ = some ⟨4,([false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]),(rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true,false,true,true] [] [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] 18 local1 n (([false,true,true,false,true,true,false,true,true])) (([false,true,false,true]))

theorem phase2 (n : Nat) : run0 table 18 ⟨4,([false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]),(rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([false,true,false,true])⟩ = some ⟨2,([false,true]),([true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([false,true,false,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 42 ⟨2,([false]) ++ (L),([true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ ([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (L),([true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (42*n) ⟨2,([false,true]),([true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([false,true,false,true])⟩ = some ⟨2,([false]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([true]),([true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] 42 local3 n (([true])) (([false,true,false,true]))

theorem phase4 (n : Nat) : run0 table 97 ⟨2,([false]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([true]),([true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,true,false,true])⟩ = some ⟨4,([false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([true]),([false,true,false,true])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 18 ⟨4,([false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ ([false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (L),([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (18*n) ⟨4,([false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([true]),([false,true,false,true])⟩ = some ⟨4,([false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,true]),(rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] [] [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] 18 local5 n (([true])) (([false,true,false,true]))

theorem phase6 (n : Nat) : run0 table 28 ⟨4,([false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,true]),(rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([false,true,false,true])⟩ = some ⟨1,([false,true]),([true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([false,true,false,true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 42 ⟨1,([false]) ++ (L),([true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ ([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ = some ⟨1,([false]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),([true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (42*n) ⟨1,([false,true]),([true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([false,true,false,true])⟩ = some ⟨1,([false]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] 42 local7 n (([true])) (([false,true,false,true]))

theorem phase8 (n : Nat) : run0 table 61 ⟨1,([false]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,true,false,true])⟩ = some ⟨4,([false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]) = ([false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true,true,false,true,true]) := by
  calc
    _ = ([false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] (n)) ++ ([true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false])) (([true])) [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] true n
    _ = ([false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true])) (([true,true])) [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] false n
    _ = ([false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true])) (([false,true,true])) [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] true n
    _ = ([false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] (n)) ++ ([true,true,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false])) (([true,false,true,true])) [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] true n
    _ = ([false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true])) (([true,true,false,true,true])) [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] false n
    _ = ([false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true,false,true,true,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true])) (([false,true,true,false,true,true])) [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] true n
    _ = ([false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] (n)) ++ ([true,true,false,true,true,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false])) (([true,false,true,true,false,true,true])) [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] true n
    _ = ([false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] (n)) ++ ([false,true,true,false,true,true,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true])) (([true,true,false,true,true,false,true,true])) [true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (256+120*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalL n] at H
  rw [show 52+18*n+18+42*n+97+18*n+28+42*n+61=256+120*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 80 (fun n => 256+120*n) entry (by intro n; omega) growth m hm

#print axioms never

end M9673

end BB6.Agent11Raw121Pumps
