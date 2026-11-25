import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B1RCPumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M1123

-- 1RB1RC_1RC---_0RD1LE_1LD0RA_0LF0LE_0RB1LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩

theorem entry : run0 table 14 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 13 ⟨4,[],([false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ = some ⟨2,([false,true,false,true,false]),([false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 65 ⟨2,([false,true,false]) ++ (L),([false,true]) ++ ([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ = some ⟨2,([false,true,false]) ++ ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (L),([false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (65*n) ⟨2,([false,true,false,true,false]),([false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ = some ⟨2,([false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)) ++ ([true,false]),([false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false,true,false] [false,true] [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] 65 local1 n (([true,false])) ([])

theorem phase2 (n : Nat) : run0 table 32 ⟨2,([false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)) ++ ([true,false]),([false,true])⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)) ++ ([true,false]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 25 ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (L),(R)⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ (L),([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (25*n) ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)) ++ ([true,false]),[]⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false,true,false]),(rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 2 [true,true,false,true,false,false,true,false,false,true,false] [] [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] 25 local3 n (([true,false])) ([])

theorem phase4 (n : Nat) : run0 table 21 ⟨2,([true,true,false,true,false,false,true,false,false,true,false,true,false]),(rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ = some ⟨2,([false,true,false]),([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 65 ⟨2,([false,true,false]) ++ (L),([false,true,false,false,true,false,false,true,false,false,true]) ++ ([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ = some ⟨2,([false,true,false]) ++ ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (L),([false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (65*n) ⟨2,([false,true,false]),([false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ = some ⟨2,([false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)),([false,true,false,false,true,false,false,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false,true,false] [false,true,false,false,true,false,false,true,false,false,true] [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] 65 local5 n ([]) ([])

theorem phase6 (n : Nat) : run0 table 71 ⟨2,([false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)),([false,true,false,false,true,false,false,true,false,false,true])⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)),[]⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 25 ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (L),(R)⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (L),([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (25*n) ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)),[]⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]),(rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 2 [true,true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] [] [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] 25 local7 n ([]) ([])

theorem phase8 (n : Nat) : run0 table 32 ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]),(rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ = some ⟨4,[],([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n)) = ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (169+180*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 13+65*n+32+25*n+21+65*n+71+25*n+32=169+180*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 14 (fun n => 169+180*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1123

namespace M1124

-- 1RB1RC_1RC---_0RD1LE_1LD0RA_0LF0LE_1RD1LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩

theorem entry : run0 table 14 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 15 ⟨4,[],([false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ = some ⟨3,([true,true,false]),([true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 75 ⟨3,([true]) ++ (L),([true,false,false,true]) ++ ([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (L),([true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (75*n) ⟨3,([true,true,false]),([true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)) ++ ([true,false]),([true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true,false,false,true] [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] 75 local1 n (([true,false])) ([])

theorem phase2 (n : Nat) : run0 table 38 ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)) ++ ([true,false]),([true,false,false,true])⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)) ++ ([true,false]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 25 ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (L),(R)⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ (L),([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (25*n) ⟨2,([true,true,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)) ++ ([true,false]),[]⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false,true,false]),(rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 2 [true,true,false,true,false,false,true,false,false,true,false] [] [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] 25 local3 n (([true,false])) ([])

theorem phase4 (n : Nat) : run0 table 21 ⟨2,([true,true,false,true,false,false,true,false,false,true,false,true,false]),(rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ = some ⟨3,([true]),([true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 75 ⟨3,([true]) ++ (L),([true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ ([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (L),([true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (75*n) ⟨3,([true]),([true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)),([true,false,false,true,false,false,true,false,false,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true,false,false,true,false,false,true,false,false,true,false,false,true] [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] 75 local5 n ([]) ([])

theorem phase6 (n : Nat) : run0 table 83 ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)),([true,false,false,true,false,false,true,false,false,true,false,false,true])⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)),[]⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 25 ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (L),(R)⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (L),([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (25*n) ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] (n)),[]⟩ = some ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]),(rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 2 [true,true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] [] [false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] 25 local7 n ([]) ([])

theorem phase8 (n : Nat) : run0 table 32 ⟨2,([true,true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]),(rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ = some ⟨4,[],([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n)) = ([false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (189+200*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [show 15+75*n+38+25*n+21+75*n+83+25*n+32=189+200*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 14 (fun n => 189+200*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1124

namespace M1139

-- 1RB1RC_1RC1RF_0RD1LE_1LD0RA_1LA0LE_0RC---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,([false,false,false,true,false,false,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)),[]⟩

theorem entry : run0 table 32 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 39 ⟨0,([false,false,false,true,false,false,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)),[]⟩ = some ⟨4,([true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)),([true,false,true,true,true,true,false,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 20 ⟨4,([true,false,true,true]) ++ ([false,true,true,false,true,true,false,true,true,false,true,true]) ++ (L),(R)⟩ = some ⟨4,([true,false,true,true]) ++ (L),([false,true,false,false,true,false,false,true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (20*n) ⟨4,([true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)),([true,false,true,true,true,true,false,true])⟩ = some ⟨4,([true,false,true,true]),(rep [false,true,false,false,true,false,false,true,false,false,true,false] (n)) ++ ([true,false,true,true,true,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,true,true] [] [false,true,true,false,true,true,false,true,true,false,true,true] [false,true,false,false,true,false,false,true,false,false,true,false] 20 local1 n ([]) (([true,false,true,true,true,true,false,true]))

theorem phase2 (n : Nat) : run0 table 8 ⟨4,([true,false,true,true]),(rep [false,true,false,false,true,false,false,true,false,false,true,false] (n)) ++ ([true,false,true,true,true,true,false,true])⟩ = some ⟨1,([true,true]),([false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false] (n)) ++ ([true,false,true,true,true,true,false,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 44 ⟨1,([true]) ++ (L),([false,false,true,false]) ++ ([false,true,false,false,true,false,false,true,false,false,true,false]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),([false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (44*n) ⟨1,([true,true]),([false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false,false,true,false] (n)) ++ ([true,false,true,true,true,true,false,true])⟩ = some ⟨1,([true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([false,false,true,false,true,false,true,true,true,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,false,true,false] [false,true,false,false,true,false,false,true,false,false,true,false] [true,false,true,true,false,true,true,false,true,true,false,true] 44 local3 n (([true])) (([true,false,true,true,true,true,false,true]))

theorem phase4 (n : Nat) : run0 table 27 ⟨1,([true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([false,false,true,false,true,false,true,true,true,true,false,true])⟩ = some ⟨4,([false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([true,true,true,false,true])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 20 ⟨4,([false,true,true,false,true,true,false,true]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true,false,true,true,false,true]) ++ (L),([false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (20*n) ⟨4,([false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([true,true,true,false,true])⟩ = some ⟨4,([false,true,true,false,true,true,false,true,true]),(rep [false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([true,true,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true,false,true,true,false,true] [] [true,false,true,true,false,true,true,false,true,true,false,true] [false,false,true,false,false,true,false,false,true,false,false,true] 20 local5 n (([true])) (([true,true,true,false,true]))

theorem phase6 (n : Nat) : run0 table 17 ⟨4,([false,true,true,false,true,true,false,true,true]),(rep [false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([true,true,true,false,true])⟩ = some ⟨1,([true,true]),([false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([true,true,true,false,true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 44 ⟨1,([true]) ++ (L),([false,false,true,false,false,true,false,false,true]) ++ ([false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),([false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (44*n) ⟨1,([true,true]),([false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([true,true,true,false,true])⟩ = some ⟨1,([true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([false,false,true,false,false,true,false,false,true,true,true,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,false,true,false,false,true,false,false,true] [false,false,true,false,false,true,false,false,true,false,false,true] [true,false,true,true,false,true,true,false,true,true,false,true] 44 local7 n (([true])) (([true,true,true,false,true]))

theorem phase8 (n : Nat) : run0 table 34 ⟨1,([true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([false,false,true,false,false,true,false,false,true,true,true,true,false,true])⟩ = some ⟨4,([false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([true,true,false,true])⟩ := by rfl

theorem local9 (L R : List Bool) : run0 table 20 ⟨4,([false,true,true,false,true,true,false,true,true,false,true]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true,false,true,true,false,true,true,false,true]) ++ (L),([false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase9 (n : Nat) : run0 table (20*n) ⟨4,([false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([true,true,false,true])⟩ = some ⟨4,([false,true,true,false,true,true,false,true,true,false,true,true]),(rep [false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([true,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true,false,true,true,false,true,true,false,true] [] [true,false,true,true,false,true,true,false,true,true,false,true] [false,false,true,false,false,true,false,false,true,false,false,true] 20 local9 n (([true])) (([true,true,false,true]))

theorem phase10 (n : Nat) : run0 table 22 ⟨4,([false,true,true,false,true,true,false,true,true,false,true,true]),(rep [false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([true,true,false,true])⟩ = some ⟨1,([true,true]),([false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([true,true,false,true])⟩ := by rfl

theorem local11 (L R : List Bool) : run0 table 44 ⟨1,([true]) ++ (L),([false,false,true,false,false,true,false,false,true,false,false,true]) ++ ([false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),([false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase11 (n : Nat) : run0 table (44*n) ⟨1,([true,true]),([false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([true,true,false,true])⟩ = some ⟨1,([true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([false,false,true,false,false,true,false,false,true,false,false,true,true,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,false,true,false,false,true,false,false,true,false,false,true] [false,false,true,false,false,true,false,false,true,false,false,true] [true,false,true,true,false,true,true,false,true,true,false,true] 44 local11 n (([true])) (([true,true,false,true]))

theorem phase12 (n : Nat) : run0 table 45 ⟨1,([true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([false,false,true,false,false,true,false,false,true,false,false,true,true,true,false,true])⟩ = some ⟨4,([false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([true,false,true])⟩ := by rfl

theorem local13 (L R : List Bool) : run0 table 20 ⟨4,([false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),(R)⟩ = some ⟨4,([false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),([false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase13 (n : Nat) : run0 table (20*n) ⟨4,([false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([true,false,true])⟩ = some ⟨4,([false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]),(rep [false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,true,true,false,true,true,false,true,true,false,true,true,false,true] [] [true,false,true,true,false,true,true,false,true,true,false,true] [false,false,true,false,false,true,false,false,true,false,false,true] 20 local13 n (([true])) (([true,false,true]))

theorem phase14 (n : Nat) : run0 table 27 ⟨4,([false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]),(rep [false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([true,false,true])⟩ = some ⟨1,([true,true]),([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([true,false,true])⟩ := by rfl

theorem local15 (L R : List Bool) : run0 table 44 ⟨1,([true]) ++ (L),([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ ([false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,true,true,false,true,true,false,true,true,false,true]) ++ (L),([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (R)⟩ := by rfl

theorem phase15 (n : Nat) : run0 table (44*n) ⟨1,([true,true]),([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true,false,false,true,false,false,true] (n)) ++ ([true,false,true])⟩ = some ⟨1,([true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true] [false,false,true,false,false,true,false,false,true,false,false,true] [true,false,true,true,false,true,true,false,true,true,false,true] 44 local15 n (([true])) (([true,false,true]))

theorem phase16 (n : Nat) : run0 table 51 ⟨1,([true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,true,false,true])⟩ = some ⟨0,([false,false,false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true,true,false,true] (n)) ++ ([true]) = ([false,false,false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)) := by
  calc
    _ = ([false,false,false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true,false,true,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true])) ([]) [false,true,true,false,true,true,false,true,true,false,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (270+256*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n)) (phase9 n)) (phase10 n)) (phase11 n)) (phase12 n)) (phase13 n)) (phase14 n)) (phase15 n)) (phase16 n))
  rw [finalL n] at H
  rw [show 39+20*n+8+44*n+27+20*n+17+44*n+34+20*n+22+44*n+45+20*n+27+44*n+51=270+256*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 32 (fun n => 270+256*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1139

namespace M1143

-- 1RB1RC_1RC---_0RD1LE_1LD0RA_1LF0LE_0RA0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([true])⟩

theorem entry : run0 table 16 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨4,[],([false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([true])⟩ = some ⟨0,([true,false]),([false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 26 ⟨0,([true,false]) ++ (L),([false,false,true,false]) ++ ([false,true,false,false,true,false]) ++ (R)⟩ = some ⟨0,([true,false]) ++ ([false,true,false,false,true,false]) ++ (L),([false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (26*n) ⟨0,([true,false]),([false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([true])⟩ = some ⟨0,([true,false]) ++ (rep [false,true,false,false,true,false] (n)),([false,false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [true,false] [false,false,true,false] [false,true,false,false,true,false] [false,true,false,false,true,false] 26 local1 n ([]) (([true]))

theorem phase2 (n : Nat) : run0 table 24 ⟨0,([true,false]) ++ (rep [false,true,false,false,true,false] (n)),([false,false,true,false,true])⟩ = some ⟨4,([true,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)),([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 14 ⟨4,([true,false,true,false,false,true,false,false,true,false]) ++ ([false,true,false,false,true,false]) ++ (L),(R)⟩ = some ⟨4,([true,false,true,false,false,true,false,false,true,false]) ++ (L),([false,true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (14*n) ⟨4,([true,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)),([true])⟩ = some ⟨4,([true,false,true,false,false,true,false,false,true,false]),(rep [false,true,false,false,true,false] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,true,false,false,true,false,false,true,false] [] [false,true,false,false,true,false] [false,true,false,false,true,false] 14 local3 n ([]) (([true]))

theorem phase4 (n : Nat) : run0 table 22 ⟨4,([true,false,true,false,false,true,false,false,true,false]),(rep [false,true,false,false,true,false] (n)) ++ ([true])⟩ = some ⟨4,[],([false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([true]) = ([false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([true]) := by
  rfl

theorem growth (n : Nat) : run0 table (48+40*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 2+26*n+24+14*n+22=48+40*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 16 (fun n => 48+40*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1143

namespace M1144

-- 1RB1RC_1RC---_0RD1LE_1LD0RA_1LF0LE_1LC0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([true])⟩

theorem entry : run0 table 17 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 2 ⟨5,[],([true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([true])⟩ = some ⟨3,([true,false]),([true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 30 ⟨3,([true,false]) ++ (L),([true,false,false,true,false]) ++ ([false,true,false,false,true,false]) ++ (R)⟩ = some ⟨3,([true,false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (30*n) ⟨3,([true,false]),([true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([true])⟩ = some ⟨3,([true,false]) ++ (rep [true,false,false,true,false,false] (n)),([true,false,false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true,false] [true,false,false,true,false] [false,true,false,false,true,false] [true,false,false,true,false,false] 30 local1 n ([]) (([true]))

theorem phase2 (n : Nat) : run0 table 27 ⟨3,([true,false]) ++ (rep [true,false,false,true,false,false] (n)),([true,false,false,true,false,true])⟩ = some ⟨4,([true,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)),([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 14 ⟨4,([true,false,true,false,false,true,false,false,true,false,false]) ++ ([true,false,false,true,false,false]) ++ (L),(R)⟩ = some ⟨4,([true,false,true,false,false,true,false,false,true,false,false]) ++ (L),([false,true,false,false,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (14*n) ⟨4,([true,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)),([true])⟩ = some ⟨4,([true,false,true,false,false,true,false,false,true,false,false]),(rep [false,true,false,false,true,false] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,true,false,false,true,false,false,true,false,false] [] [true,false,false,true,false,false] [false,true,false,false,true,false] 14 local3 n ([]) (([true]))

theorem phase4 (n : Nat) : run0 table 23 ⟨4,([true,false,true,false,false,true,false,false,true,false,false]),(rep [false,true,false,false,true,false] (n)) ++ ([true])⟩ = some ⟨5,[],([true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([true]) = ([true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false] (n)) ++ ([true]) := by
  rfl

theorem growth (n : Nat) : run0 table (52+44*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [show 2+30*n+27+14*n+23=52+44*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 17 (fun n => 52+44*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1144

namespace M1154

-- 1RB1RC_1RC---_0RD1LE_1LD0RA_0LA0LF_0LC0LA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,2⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,([false,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([true,false,true,true]),[]⟩

theorem entry : run0 table 30 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 19 ⟨0,([false,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([true,false,true,true]),[]⟩ = some ⟨3,([false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([true,false,true,true]),([true,false,false,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 18 ⟨3,([false,false,true]) ++ ([false,false,true,false,false,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (18*n) ⟨3,([false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([true,false,true,true]),([true,false,false,true])⟩ = some ⟨3,([false,false,true,true,false,true,true]),(rep [true,false,true,true,false,true] (n)) ++ ([true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true] [] [false,false,true,false,false,true] [true,false,true,true,false,true] 18 local1 n (([true,false,true,true])) (([true,false,false,true]))

theorem phase2 (n : Nat) : run0 table 19 ⟨3,([false,false,true,true,false,true,true]),(rep [true,false,true,true,false,true] (n)) ++ ([true,false,false,true])⟩ = some ⟨2,([false,true,true,false,true,true]),([true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true,false,false,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨2,([false]) ++ (L),([true]) ++ ([true,false,true,true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (6*n) ⟨2,([false,true,true,false,true,true]),([true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true,false,false,true])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,true,true]),([true,true,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true] [true,false,true,true,false,true] [true,false,false,true,false,false] 6 local3 n (([true,true,false,true,true])) (([true,false,false,true]))

theorem phase4 (n : Nat) : run0 table 4 ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,true,true]),([true,true,false,false,true])⟩ = some ⟨3,([false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,true,true]),([true])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 18 ⟨3,([false,false,true,false,false]) ++ ([true,false,false,true,false,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,false,false]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (18*n) ⟨3,([false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,true,true]),([true])⟩ = some ⟨3,([false,false,true,false,false,true,true,false,true,true]),(rep [true,false,true,true,false,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,false,false] [] [true,false,false,true,false,false] [true,false,true,true,false,true] 18 local5 n (([true,true,false,true,true])) (([true]))

theorem phase6 (n : Nat) : run0 table 28 ⟨3,([false,false,true,false,false,true,true,false,true,true]),(rep [true,false,true,true,false,true] (n)) ++ ([true])⟩ = some ⟨2,([false,true,true,false,true,true]),([true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 6 ⟨2,([false]) ++ (L),([true,true,false,true]) ++ ([true,false,true,true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (6*n) ⟨2,([false,true,true,false,true,true]),([true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n)) ++ ([true])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,true,true]),([true,true,false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true] [true,false,true,true,false,true] [true,false,false,true,false,false] 6 local7 n (([true,true,false,true,true])) (([true]))

theorem phase8 (n : Nat) : run0 table 7 ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,true,true]),([true,true,false,true,true])⟩ = some ⟨3,([false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,true,true]),[]⟩ := by rfl

theorem local9 (L R : List Bool) : run0 table 18 ⟨3,([false,false,true,false,false,true,false,false]) ++ ([true,false,false,true,false,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,false,false,true,false,false]) ++ (L),([true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase9 (n : Nat) : run0 table (18*n) ⟨3,([false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,true,true]),[]⟩ = some ⟨3,([false,false,true,false,false,true,false,false,true,true,false,true,true]),(rep [true,false,true,true,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,false,false,true,false,false] [] [true,false,false,true,false,false] [true,false,true,true,false,true] 18 local9 n (([true,true,false,true,true])) ([])

theorem phase10 (n : Nat) : run0 table 37 ⟨3,([false,false,true,false,false,true,false,false,true,true,false,true,true]),(rep [true,false,true,true,false,true] (n))⟩ = some ⟨2,([false,true,true,false,true,true]),([true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n))⟩ := by rfl

theorem local11 (L R : List Bool) : run0 table 6 ⟨2,([false]) ++ (L),([true,true,false,true,true,false,true]) ++ ([true,false,true,true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,false,false]) ++ (L),([true,true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase11 (n : Nat) : run0 table (6*n) ⟨2,([false,true,true,false,true,true]),([true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true] (n))⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,true,true]),([true,true,false,true,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true,true,false,true] [true,false,true,true,false,true] [true,false,false,true,false,false] 6 local11 n (([true,true,false,true,true])) ([])

theorem phase12 (n : Nat) : run0 table 8 ⟨2,([false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,true,true]),([true,true,false,true,true,false,true])⟩ = some ⟨0,([false,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,true,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false] (n)) ++ ([true,true,false,true,true]) = ([false,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([true,false,true,true]) := by
  calc
    _ = ([false,false,false,true,false,false,true,false,false,true]) ++ (rep [false,false,true,false,false,true] (n)) ++ ([true,false,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,true,false,false,true,false,false])) (([true,false,true,true])) [false,false,true,false,false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (122+72*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n)) (phase9 n)) (phase10 n)) (phase11 n)) (phase12 n))
  rw [finalL n] at H
  rw [show 19+18*n+19+6*n+4+18*n+28+6*n+7+18*n+37+6*n+8=122+72*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 30 (fun n => 122+72*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1154

namespace M1184

-- 1RB1RC_1RC0RA_0RD1LE_1LD0RA_1LA0LF_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,([false,true]) ++ (rep [false,true] (n)) ++ (rep [false,false,true,false,true] (n)),[]⟩

theorem entry : run0 table 1 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 7 ⟨1,([false,true]) ++ (rep [false,true] (n)) ++ (rep [false,false,true,false,true] (n)),[]⟩ = some ⟨4,([true,false,true]) ++ (rep [false,true] (n)) ++ (rep [false,false,true,false,true] (n)),([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨4,([true,false,true]) ++ ([false,true]) ++ (L),(R)⟩ = some ⟨4,([true,false,true]) ++ (L),([true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨4,([true,false,true]) ++ (rep [false,true] (n)) ++ (rep [false,false,true,false,true] (n)),([true])⟩ = some ⟨4,([true,false,true]) ++ (rep [false,false,true,false,true] (n)),(rep [true,false] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,true] [] [false,true] [true,false] 2 local1 n ((rep [false,false,true,false,true] (n))) (([true]))

theorem local2 (L R : List Bool) : run0 table 7 ⟨4,([true,false,true]) ++ ([false,false,true,false,true]) ++ (L),(R)⟩ = some ⟨4,([true,false,true]) ++ (L),([true,true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (7*n) ⟨4,([true,false,true]) ++ (rep [false,false,true,false,true] (n)),(rep [true,false] (n)) ++ ([true])⟩ = some ⟨4,([true,false,true]),(rep [true,true,false,true,false] (n)) ++ (rep [true,false] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,true] [] [false,false,true,false,true] [true,true,false,true,false] 7 local2 n ([]) ((rep [true,false] (n)) ++ ([true]))

theorem phase3 (n : Nat) : run0 table 6 ⟨4,([true,false,true]),(rep [true,true,false,true,false] (n)) ++ (rep [true,false] (n)) ++ ([true])⟩ = some ⟨1,([true,true]),([true,false,true,false]) ++ (rep [true,true,false,true,false] (n)) ++ (rep [true,false] (n)) ++ ([true])⟩ := by rfl

theorem local4 (L R : List Bool) : run0 table 5 ⟨1,([true]) ++ (L),([true,false,true,false]) ++ ([true,true,false,true,false]) ++ (R)⟩ = some ⟨1,([true]) ++ ([true,false,false,true,false]) ++ (L),([true,false,true,false]) ++ (R)⟩ := by rfl

theorem phase4 (n : Nat) : run0 table (5*n) ⟨1,([true,true]),([true,false,true,false]) ++ (rep [true,true,false,true,false] (n)) ++ (rep [true,false] (n)) ++ ([true])⟩ = some ⟨1,([true]) ++ (rep [true,false,false,true,false] (n)) ++ ([true]),([true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [true] [true,false,true,false] [true,true,false,true,false] [true,false,false,true,false] 5 local4 n (([true])) ((rep [true,false] (n)) ++ ([true]))

theorem phase5 (n : Nat) : run0 table 4 ⟨1,([true]) ++ (rep [true,false,false,true,false] (n)) ++ ([true]),([true,false,true,false]) ++ (rep [true,false] (n)) ++ ([true])⟩ = some ⟨0,([false,false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([true]),(rep [true,false] (n)) ++ ([true])⟩ := by rfl

theorem local6 (L R : List Bool) : run0 table 2 ⟨0,([false]) ++ (L),([true,false]) ++ (R)⟩ = some ⟨0,([false]) ++ ([false,true]) ++ (L),(R)⟩ := by rfl

theorem phase6 (n : Nat) : run0 table (2*n) ⟨0,([false,false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([true]),(rep [true,false] (n)) ++ ([true])⟩ = some ⟨0,([false]) ++ (rep [false,true] (n)) ++ ([false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([true]),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [false] [] [true,false] [false,true] 2 local6 n (([false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([true])) (([true]))

theorem phase7 (n : Nat) : run0 table 3 ⟨0,([false]) ++ (rep [false,true] (n)) ++ ([false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([true]),([true])⟩ = some ⟨1,([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([true]) = ([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([false,false,true,false,true]) ++ (rep [false,false,true,false,true] (n)) := by
  calc
    _ = ([false,true,false]) ++ (rep [true,false] (n)) ++ ([true,false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false])) (([false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([true])) [false] true n
    _ = ([false,true]) ++ (rep [false,true] (n)) ++ ([false,true,false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([true,false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([true])) [true] false n
    _ = ([false]) ++ (rep [true,false] (n)) ++ ([true,false,true,false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,true,false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([true])) [false] true n
    _ = (rep [false,true] (n)) ++ ([false,true,false,true,false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,false,true,false,false,true,false]) ++ (rep [true,false,false,true,false] (n)) ++ ([true])) [true] false n
    _ = (rep [false,true] (n)) ++ ([false,true,false,true,false,false,true,false,true]) ++ (rep [false,false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ((rep [false,true] (n)) ++ ([false,true,false,true,false,false,true,false])) ([]) [false,false,true,false] true n
    _ = ([false]) ++ (rep [true,false] (n)) ++ ([true,false,true,false,false,true,false,true]) ++ (rep [false,false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,false,true,false,false,true,false,true]) ++ (rep [false,false,true,false,true] (n))) [true] false n
    _ = ([false,true]) ++ (rep [false,true] (n)) ++ ([false,true,false,false,true,false,true]) ++ (rep [false,false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,true,false,false,true,false,true]) ++ (rep [false,false,true,false,true] (n))) [false] true n
    _ = ([false,true,false]) ++ (rep [true,false] (n)) ++ ([true,false,false,true,false,true]) ++ (rep [false,false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([true,false,false,true,false,true]) ++ (rep [false,false,true,false,true] (n))) [true] false n
    _ = ([false,true,false,true]) ++ (rep [false,true] (n)) ++ ([false,false,true,false,true]) ++ (rep [false,false,true,false,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false])) (([false,false,true,false,true]) ++ (rep [false,false,true,false,true] (n))) [false] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (20+16*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n))
  rw [finalL n] at H
  rw [show 7+2*n+7*n+6+5*n+4+2*n+3=20+16*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1 (fun n => 20+16*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1184

namespace M1194

-- 1RB1RC_1RC0RF_0RD1LE_1LD0RA_1LC0LF_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,([false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)),[]⟩

theorem entry : run0 table 20 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem local0 (L R : List Bool) : run0 table 27 ⟨5,([false,false,true,false,false,true,false,false]) ++ ([true,false,false,true,false,false,true,false,false]) ++ (L),(R)⟩ = some ⟨5,([false,false,true,false,false,true,false,false]) ++ (L),([false,true,true,false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (27*n) ⟨5,([false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)),[]⟩ = some ⟨5,([false,false,true,false,false,true,false,false]),(rep [false,true,true,false,true,true,false,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,true,false,false,true,false,false] [] [true,false,false,true,false,false,true,false,false] [false,true,true,false,true,true,false,true,true] 27 local0 n ([]) ([])

theorem phase1 (n : Nat) : run0 table 21 ⟨5,([false,false,true,false,false,true,false,false]),(rep [false,true,true,false,true,true,false,true,true] (n))⟩ = some ⟨3,([true,false]),([true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true] (n))⟩ := by rfl

theorem local2 (L R : List Bool) : run0 table 9 ⟨3,([true]) ++ (L),([true,false,true,true,false,true,true]) ++ ([false,true,true,false,true,true,false,true,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,false,false,true,false,false,true,false]) ++ (L),([true,false,true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase2 (n : Nat) : run0 table (9*n) ⟨3,([true,false]),([true,false,true,true,false,true,true]) ++ (rep [false,true,true,false,true,true,false,true,true] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true,false,true,true,false,true,true] [false,true,true,false,true,true,false,true,true] [false,true,false,false,true,false,false,true,false] 9 local2 n (([false])) ([])

theorem phase3 (n : Nat) : run0 table 32 ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true,true])⟩ = some ⟨4,([true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true])⟩ := by rfl

theorem local4 (L R : List Bool) : run0 table 27 ⟨4,([true,false,false,true,false,false,true,false,false,true,false]) ++ ([false,true,false,false,true,false,false,true,false]) ++ (L),(R)⟩ = some ⟨4,([true,false,false,true,false,false,true,false,false,true,false]) ++ (L),([true,true,false,true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase4 (n : Nat) : run0 table (27*n) ⟨4,([true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true])⟩ = some ⟨4,([true,false,false,true,false,false,true,false,false,true,false,false]),(rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,false,true,false,false,true,false,false,true,false] [] [false,true,false,false,true,false,false,true,false] [true,true,false,true,true,false,true,true,false] 27 local4 n (([false])) (([true,false,true]))

theorem phase5 (n : Nat) : run0 table 31 ⟨4,([true,false,false,true,false,false,true,false,false,true,false,false]),(rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false,true])⟩ = some ⟨3,([true,false]),([true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false,true])⟩ := by rfl

theorem local6 (L R : List Bool) : run0 table 9 ⟨3,([true]) ++ (L),([true,false,true,true,false,true,true,false,true,true,false]) ++ ([true,true,false,true,true,false,true,true,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,false,false,true,false,false,true,false]) ++ (L),([true,false,true,true,false,true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase6 (n : Nat) : run0 table (9*n) ⟨3,([true,false]),([true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false,true])⟩ = some ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true,true,false,true,true,false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true,false,true,true,false,true,true,false,true,true,false] [true,true,false,true,true,false,true,true,false] [false,true,false,false,true,false,false,true,false] 9 local6 n (([false])) (([true,false,true]))

theorem phase7 (n : Nat) : run0 table 15 ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true,true,false,true,true,false,true,false,true])⟩ = some ⟨5,([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]) = ([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) := by
  calc
    _ = ([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false])) ([]) [true,false,false,true,false,false,true,false] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (99+72*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n))
  rw [finalL n] at H
  rw [show 27*n+21+9*n+32+27*n+31+9*n+15=99+72*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 20 (fun n => 99+72*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1194

namespace M1198

-- 1RB1RC_1RC1RC_0RD1LE_1LD0RA_1LC0LF_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,[],([true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([false,true])⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 1 ⟨2,[],([true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([false,true])⟩ = some ⟨3,([true,false]),([true,false,true]) ++ (rep [true,false,true] (n)) ++ ([false,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨3,([true]) ++ (L),([true,false,true]) ++ ([true,false,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,false]) ++ (L),([true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨3,([true,false]),([true,false,true]) ++ (rep [true,false,true] (n)) ++ ([false,true])⟩ = some ⟨3,([true]) ++ (rep [false,true,false] (n)) ++ ([false]),([true,false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true,false,true] [true,false,true] [false,true,false] 3 local1 n (([false])) (([false,true]))

theorem phase2 (n : Nat) : run0 table 14 ⟨3,([true]) ++ (rep [false,true,false] (n)) ++ ([false]),([true,false,true,false,true])⟩ = some ⟨4,([true,false,false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false]),([true,false,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 9 ⟨4,([true,false,false,true,false]) ++ ([false,true,false]) ++ (L),(R)⟩ = some ⟨4,([true,false,false,true,false]) ++ (L),([true,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (9*n) ⟨4,([true,false,false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false]),([true,false,true])⟩ = some ⟨4,([true,false,false,true,false,false]),(rep [true,true,false] (n)) ++ ([true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,false,true,false] [] [false,true,false] [true,true,false] 9 local3 n (([false])) (([true,false,true]))

theorem phase4 (n : Nat) : run0 table 12 ⟨4,([true,false,false,true,false,false]),(rep [true,true,false] (n)) ++ ([true,false,true])⟩ = some ⟨2,[],([true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true,false,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true,false,true]) = ([true,true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([false,true]) := by
  calc
    _ = ([true,true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true,false,true,true,false])) (([false,true])) [true,false] true n

theorem growth (n : Nat) : run0 table (27+12*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 1+3*n+14+9*n+12=27+12*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 27+12*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1198

namespace M1199

-- 1RB1RC_1RC1RD_0RD1LE_1LD0RA_1LC0LF_1LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,([false,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)),[]⟩

theorem entry : run0 table 61 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 10 ⟨0,([false,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)),[]⟩ = some ⟨4,([true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)),([true,false,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 27 ⟨4,([true,false,false,true,false,false,true,false,false,true,false,false]) ++ ([true,false,false,true,false,false,true,false,false]) ++ (L),(R)⟩ = some ⟨4,([true,false,false,true,false,false,true,false,false,true,false,false]) ++ (L),([true,true,false,true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (27*n) ⟨4,([true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)),([true,false,true])⟩ = some ⟨4,([true,false,false,true,false,false,true,false,false,true,false,false]),(rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,false,false,true,false,false,true,false,false,true,false,false] [] [true,false,false,true,false,false,true,false,false] [true,true,false,true,true,false,true,true,false] 27 local1 n ([]) (([true,false,true]))

theorem phase2 (n : Nat) : run0 table 31 ⟨4,([true,false,false,true,false,false,true,false,false,true,false,false]),(rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false,true])⟩ = some ⟨3,([true,false]),([true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 9 ⟨3,([true]) ++ (L),([true,false,true,true,false,true,true,false,true,true,false]) ++ ([true,true,false,true,true,false,true,true,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,false,false,true,false,false,true,false]) ++ (L),([true,false,true,true,false,true,true,false,true,true,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (9*n) ⟨3,([true,false]),([true,false,true,true,false,true,true,false,true,true,false]) ++ (rep [true,true,false,true,true,false,true,true,false] (n)) ++ ([true,false,true])⟩ = some ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true,true,false,true,true,false,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true,false,true,true,false,true,true,false,true,true,false] [true,true,false,true,true,false,true,true,false] [false,true,false,false,true,false,false,true,false] 9 local3 n (([false])) (([true,false,true]))

theorem phase4 (n : Nat) : run0 table 21 ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true,true,false,true,true,false,true,false,true])⟩ = some ⟨3,([true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,true])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 27 ⟨3,([true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ ([false,true,false,false,true,false,false,true,false]) ++ (L),([true,true]) ++ (R)⟩ = some ⟨3,([true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (L),([true,true]) ++ ([true,false,true,true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (27*n) ⟨3,([true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,true])⟩ = some ⟨3,([true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]),([true,true]) ++ (rep [true,false,true,true,false,true,true,false,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false] [true,true] [false,true,false,false,true,false,false,true,false] [true,false,true,true,false,true,true,false,true] 27 local5 n (([false])) ([])

theorem phase6 (n : Nat) : run0 table 52 ⟨3,([true,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]),([true,true]) ++ (rep [true,false,true,true,false,true,true,false,true] (n))⟩ = some ⟨3,([true,false]),([true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true] (n))⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 9 ⟨3,([true]) ++ (L),([true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ ([true,false,true,true,false,true,true,false,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,false,false,true,false,false,true,false]) ++ (L),([true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (9*n) ⟨3,([true,false]),([true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true]) ++ (rep [true,false,true,true,false,true,true,false,true] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] [true,false,true,true,false,true,true,false,true] [false,true,false,false,true,false,false,true,false] 9 local7 n (([false])) ([])

theorem phase8 (n : Nat) : run0 table 19 ⟨3,([true]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),([true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true])⟩ = some ⟨0,([false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false]) ++ (rep [false,true,false,false,true,false,false,true,false] (n)) ++ ([false]) = ([false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) := by
  calc
    _ = ([false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false]) ++ (rep [true,false,false,true,false,false,true,false,false] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false])) ([]) [true,false,false,true,false,false,true,false] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem growth (n : Nat) : run0 table (133+72*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalL n] at H
  rw [show 10+27*n+31+9*n+21+27*n+52+9*n+19=133+72*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 61 (fun n => 133+72*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1199

end BB6.Agent11Raw39B1RCPumps
