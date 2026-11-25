import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39RCPumps
open BB6Coverage BB6Coverage.Agent31Pump


namespace M1076

-- 1RB0RC_1RC0LE_0RD1LE_1LD0RA_1LF0RD_0LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,3⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([false,false,true,true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩

theorem entry : run0 table 11 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 9 ⟨4,[],([false,false,true,true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ = some ⟨3,([true,false,true,false,false,true]),([true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 72 ⟨3,([true]) ++ (L),([true]) ++ ([false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (72*n) ⟨3,([true,false,true,false,false,true]),([true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false] (n)) ++ ([false,true,false,false,true]),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true] [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] [false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false] 72 local1 n (([false,true,false,false,true])) ([])

theorem phase2 (n : Nat) : run0 table 3 ⟨3,([true]) ++ (rep [false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false] (n)) ++ ([false,true,false,false,true]),([true])⟩ = some ⟨3,([false,false,false,false]) ++ (rep [false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false] (n)) ++ ([false,true,false,false,true]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 36 ⟨3,([false,false,false,false]) ++ ([false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,false]) ++ (L),([false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (36*n) ⟨3,([false,false,false,false]) ++ (rep [false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false] (n)) ++ ([false,true,false,false,true]),[]⟩ = some ⟨3,([false,false,false,false,false,true,false,false,true]),(rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,false] [] [false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false] [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] 36 local3 n (([false,true,false,false,true])) ([])

theorem phase4 (n : Nat) : run0 table 11 ⟨3,([false,false,false,false,false,true,false,false,true]),(rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ = some ⟨2,([false,true,false,true]),([true,true,true,true,true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 72 ⟨2,([false]) ++ (L),([true,true,true,true,true]) ++ ([false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true]) ++ (L),([true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (72*n) ⟨2,([false,true,false,true]),([true,true,true,true,true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ = some ⟨2,([false]) ++ (rep [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] (n)) ++ ([true,false,true]),([true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,true,true,true] [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] 72 local5 n (([true,false,true])) ([])

theorem phase6 (n : Nat) : run0 table 25 ⟨2,([false]) ++ (rep [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] (n)) ++ ([true,false,true]),([true,true,true,true,true])⟩ = some ⟨3,([false,false,false,false,false,true,true,true]) ++ (rep [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] (n)) ++ ([true,false,true]),[]⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 36 ⟨3,([false,false,false,false,false,true,true,true]) ++ ([false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,false,false,true,true,true]) ++ (L),([false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (36*n) ⟨3,([false,false,false,false,false,true,true,true]) ++ (rep [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] (n)) ++ ([true,false,true]),[]⟩ = some ⟨3,([false,false,false,false,false,true,true,true,true,false,true]),(rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,false,false,true,true,true] [] [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] 36 local7 n (([true,false,true])) ([])

theorem phase8 (n : Nat) : run0 table 14 ⟨3,([false,false,false,false,false,true,true,true,true,false,true]),(rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ = some ⟨3,([true,false,true]),([true,true,false,true,true,true,true,true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ := by rfl

theorem local9 (L R : List Bool) : run0 table 72 ⟨3,([true,false]) ++ (L),([true,true,false,true,true,true,true,true]) ++ ([false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (R)⟩ = some ⟨3,([true,false]) ++ ([true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true]) ++ (L),([true,true,false,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase9 (n : Nat) : run0 table (72*n) ⟨3,([true,false,true]),([true,true,false,true,true,true,true,true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ = some ⟨3,([true,false]) ++ (rep [true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true] (n)) ++ ([true]),([true,true,false,true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true,false] [true,true,false,true,true,true,true,true] [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] [true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true] 72 local9 n (([true])) ([])

theorem phase10 (n : Nat) : run0 table 34 ⟨3,([true,false]) ++ (rep [true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true] (n)) ++ ([true]),([true,true,false,true,true,true,true,true])⟩ = some ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true]) ++ (rep [true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem local11 (L R : List Bool) : run0 table 36 ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true]) ++ ([true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true]) ++ (L),([false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase11 (n : Nat) : run0 table (36*n) ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true]) ++ (rep [true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true] (n)) ++ ([true]),[]⟩ = some ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true]),(rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,false,false,true,true,true,false,false,false,true] [] [true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true] [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] 36 local11 n (([true])) ([])

theorem phase12 (n : Nat) : run0 table 32 ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true]),(rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ = some ⟨3,([true,false,true,false,false,true]),([true,true,true,true,false,true,true,true,true,true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ := by rfl

theorem local13 (L R : List Bool) : run0 table 72 ⟨3,([true,false]) ++ (L),([true,true,true,true,false,true,true,true,true,true]) ++ ([false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (R)⟩ = some ⟨3,([true,false]) ++ ([false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true]) ++ (L),([true,true,true,true,false,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase13 (n : Nat) : run0 table (72*n) ⟨3,([true,false,true,false,false,true]),([true,true,true,true,false,true,true,true,true,true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ = some ⟨3,([true,false]) ++ (rep [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] (n)) ++ ([true,false,false,true]),([true,true,true,true,false,true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true,false] [true,true,true,true,false,true,true,true,true,true] [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] 72 local13 n (([true,false,false,true])) ([])

theorem phase14 (n : Nat) : run0 table 48 ⟨3,([true,false]) ++ (rep [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] (n)) ++ ([true,false,false,true]),([true,true,true,true,false,true,true,true,true,true])⟩ = some ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true]) ++ (rep [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] (n)) ++ ([true,false,false,true]),[]⟩ := by rfl

theorem local15 (L R : List Bool) : run0 table 36 ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true]) ++ ([false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true]) ++ (L),([false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase15 (n : Nat) : run0 table (36*n) ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true]) ++ (rep [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] (n)) ++ ([true,false,false,true]),[]⟩ = some ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true,true,false,false,true]),(rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,false,false,true,true,true,false,false,false,true,true,true] [] [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] 36 local15 n (([true,false,false,true])) ([])

theorem phase16 (n : Nat) : run0 table 26 ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true,true,false,false,true]),(rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ = some ⟨3,([true,false,false,true]),([true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ := by rfl

theorem local17 (L R : List Bool) : run0 table 72 ⟨3,([true,false]) ++ (L),([true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ ([false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (R)⟩ = some ⟨3,([true,false]) ++ ([true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true]) ++ (L),([true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase17 (n : Nat) : run0 table (72*n) ⟨3,([true,false,false,true]),([true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ = some ⟨3,([true,false]) ++ (rep [true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true] (n)) ++ ([false,true]),([true,true,false,true,true,true,true,true,false,true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true,false] [true,true,false,true,true,true,true,true,false,true,true,true,true,true] [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] [true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true] 72 local17 n (([false,true])) ([])

theorem phase18 (n : Nat) : run0 table 58 ⟨3,([true,false]) ++ (rep [true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true] (n)) ++ ([false,true]),([true,true,false,true,true,true,true,true,false,true,true,true,true,true])⟩ = some ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true]) ++ (rep [true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true] (n)) ++ ([false,true]),[]⟩ := by rfl

theorem local19 (L R : List Bool) : run0 table 36 ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true]) ++ ([true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true]) ++ (L),([false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase19 (n : Nat) : run0 table (36*n) ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true]) ++ (rep [true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true] (n)) ++ ([false,true]),[]⟩ = some ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,false,true]),(rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true] [] [true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true] [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] 36 local19 n (([false,true])) ([])

theorem phase20 (n : Nat) : run0 table 35 ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,false,true]),(rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ = some ⟨2,([false,true,true]),([true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ := by rfl

theorem local21 (L R : List Bool) : run0 table 72 ⟨2,([false]) ++ (L),([true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ ([false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true]) ++ (L),([true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase21 (n : Nat) : run0 table (72*n) ⟨2,([false,true,true]),([true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ = some ⟨2,([false]) ++ (rep [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] (n)) ++ ([true,true]),([true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] 72 local21 n (([true,true])) ([])

theorem phase22 (n : Nat) : run0 table 73 ⟨2,([false]) ++ (rep [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] (n)) ++ ([true,true]),([true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true])⟩ = some ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true]) ++ (rep [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] (n)) ++ ([true,true]),[]⟩ := by rfl

theorem local23 (L R : List Bool) : run0 table 36 ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true]) ++ ([false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true]) ++ (L),([false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase23 (n : Nat) : run0 table (36*n) ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true]) ++ (rep [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] (n)) ++ ([true,true]),[]⟩ = some ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,true,true]),(rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] [] [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] 36 local23 n (([true,true])) ([])

theorem phase24 (n : Nat) : run0 table 44 ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,true,true]),(rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ = some ⟨4,[],([false,false,true,true,false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,true,true,false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n)) = ([false,false,true,true,false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (412+648*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n)) (phase9 n)) (phase10 n)) (phase11 n)) (phase12 n)) (phase13 n)) (phase14 n)) (phase15 n)) (phase16 n)) (phase17 n)) (phase18 n)) (phase19 n)) (phase20 n)) (phase21 n)) (phase22 n)) (phase23 n)) (phase24 n))
  rw [show 9+72*n+3+36*n+11+72*n+25+36*n+14+72*n+34+36*n+32+72*n+48+36*n+26+72*n+58+36*n+35+72*n+73+36*n+44=412+648*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 11 (fun n => 412+648*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1076

namespace M1086

-- 1RB0RC_1RC1LB_0RD1LE_1LD0RA_1LF0LF_0LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([false,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩

theorem entry : run0 table 56 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 11 ⟨5,[],([false,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨2,([false,true]),([true,true,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 7 ⟨2,([false]) ++ (L),([true,true,true]) ++ ([true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (7*n) ⟨2,([false,true]),([true,true,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨2,([false]) ++ (rep [true] (n)) ++ ([true]),([true,true,true,false,true,true,true,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,true] [true] [true] 7 local1 n (([true])) (([false,true,true,true,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true]))

theorem phase2 (n : Nat) : run0 table 31 ⟨2,([false]) ++ (rep [true] (n)) ++ ([true]),([true,true,true,false,true,true,true,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨2,([false,true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 17 ⟨2,([false]) ++ (L),([true,true,true,true]) ++ ([false,true,true,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([false,false,false,true,true]) ++ (L),([true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (17*n) ⟨2,([false,true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨2,([false]) ++ (rep [false,false,false,true,true] (n)) ++ ([true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,true,true] [false,true,true,true,true] [false,false,false,true,true] 17 local3 n (([true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true])) (([true]))

theorem phase4 (n : Nat) : run0 table 28 ⟨2,([false]) ++ (rep [false,false,false,true,true] (n)) ++ ([true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true,true,true,true,true])⟩ = some ⟨3,([false,false,true,true,true]) ++ (rep [false,false,false,true,true] (n)) ++ ([true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true,true,true])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 15 ⟨3,([false,false,true,true,true]) ++ ([false,false,false,true,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true,true]) ++ (L),([true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (15*n) ⟨3,([false,false,true,true,true]) ++ (rep [false,false,false,true,true] (n)) ++ ([true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true,true,true])⟩ = some ⟨3,([false,false,true,true,true,true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),(rep [true,true,false,true,true] (n)) ++ ([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true,true] [] [false,false,false,true,true] [true,true,false,true,true] 15 local5 n (([true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true])) (([true,true,true]))

theorem phase6 (n : Nat) : run0 table 25 ⟨3,([false,false,true,true,true,true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),(rep [true,true,false,true,true] (n)) ++ ([true,true,true])⟩ = some ⟨1,([true]) ++ (rep [true] (n)) ++ ([true]),([false,true,true,true,true,true,true,true,false,true,true]) ++ (rep [true,true,false,true,true] (n)) ++ ([true,true,true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 1 ⟨1,([true]) ++ ([true]) ++ (L),(R)⟩ = some ⟨1,([true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (1*n) ⟨1,([true]) ++ (rep [true] (n)) ++ ([true]),([false,true,true,true,true,true,true,true,false,true,true]) ++ (rep [true,true,false,true,true] (n)) ++ ([true,true,true])⟩ = some ⟨1,([true,true]),(rep [true] (n)) ++ ([false,true,true,true,true,true,true,true,false,true,true]) ++ (rep [true,true,false,true,true] (n)) ++ ([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true] [] [true] [true] 1 local7 n (([true])) (([false,true,true,true,true,true,true,true,false,true,true]) ++ (rep [true,true,false,true,true] (n)) ++ ([true,true,true]))

theorem phase8 (n : Nat) : run0 table 5 ⟨1,([true,true]),(rep [true] (n)) ++ ([false,true,true,true,true,true,true,true,false,true,true]) ++ (rep [true,true,false,true,true] (n)) ++ ([true,true,true])⟩ = some ⟨5,[],([false,true,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true,false,true,true]) ++ (rep [true,true,false,true,true] (n)) ++ ([true,true,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,true,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true,false,true,true]) ++ (rep [true,true,false,true,true] (n)) ++ ([true,true,true]) = ([false,true,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true,false,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true]) := by
  calc
    _ = ([false,true]) ++ (rep [true] (n)) ++ ([true,false,true,true,true,true,true,true,true,false,true,true]) ++ (rep [true,true,false,true,true] (n)) ++ ([true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([false,true,true,true,true,true,true,true,false,true,true]) ++ (rep [true,true,false,true,true] (n)) ++ ([true,true,true])) [] true n
    _ = ([false]) ++ (rep [true] (n)) ++ ([true,true,false,true,true,true,true,true,true,true,false,true,true]) ++ (rep [true,true,false,true,true] (n)) ++ ([true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([true,false,true,true,true,true,true,true,true,false,true,true]) ++ (rep [true,true,false,true,true] (n)) ++ ([true,true,true])) [] true n
    _ = ([false]) ++ (rep [true] (n)) ++ ([true,true,false,true,true,true,true,true,true,true,false,true,true,true]) ++ (rep [true,false,true,true,true] (n)) ++ ([true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false]) ++ (rep [true] (n)) ++ ([true,true,false,true,true,true,true,true,true,true,false,true,true])) (([true,true])) [true,false,true,true] true n
    _ = ([false]) ++ (rep [true] (n)) ++ ([true,true,false,true,true,true,true,true,true,true,false,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false]) ++ (rep [true] (n)) ++ ([true,true,false,true,true,true,true,true,true,true,false,true,true,true])) (([true])) [false,true,true,true] true n
    _ = ([false,true]) ++ (rep [true] (n)) ++ ([true,false,true,true,true,true,true,true,true,false,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([true,false,true,true,true,true,true,true,true,false,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])) [] true n
    _ = ([false,true,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true,false,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([false,true,true,true,true,true,true,true,false,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])) [] true n

theorem growth (n : Nat) : run0 table (100+40*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalR n] at H
  rw [show 11+7*n+31+17*n+28+15*n+25+1*n+5=100+40*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 56 (fun n => 100+40*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1086

namespace M1087

-- 1RB0RC_1RC1LB_0RD1LE_1LD0RA_1LF1LE_0LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([true,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩

theorem entry : run0 table 48 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 3 ⟨4,[],([true,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨2,([false,true]),([true,true,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 7 ⟨2,([false]) ++ (L),([true,true,true]) ++ ([true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (7*n) ⟨2,([false,true]),([true,true,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨2,([false]) ++ (rep [true] (n)) ++ ([true]),([true,true,true,false,true,true,true,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,true] [true] [true] 7 local1 n (([true])) (([false,true,true,true,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true]))

theorem phase2 (n : Nat) : run0 table 31 ⟨2,([false]) ++ (rep [true] (n)) ++ ([true]),([true,true,true,false,true,true,true,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨2,([false,true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 17 ⟨2,([false]) ++ (L),([true,true,true,true]) ++ ([false,true,true,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([false,false,false,true,true]) ++ (L),([true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (17*n) ⟨2,([false,true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨2,([false]) ++ (rep [false,false,false,true,true] (n)) ++ ([true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,true,true] [false,true,true,true,true] [false,false,false,true,true] 17 local3 n (([true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true])) (([true]))

theorem phase4 (n : Nat) : run0 table 33 ⟨2,([false]) ++ (rep [false,false,false,true,true] (n)) ++ ([true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true,true,true,true,true])⟩ = some ⟨4,([false,false,true,true]) ++ (rep [false,false,false,true,true] (n)) ++ ([true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true,true,true,true])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 7 ⟨4,([false,false,true,true]) ++ ([false,false,false,true,true]) ++ (L),(R)⟩ = some ⟨4,([false,false,true,true]) ++ (L),([true,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (7*n) ⟨4,([false,false,true,true]) ++ (rep [false,false,false,true,true] (n)) ++ ([true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true,true,true,true])⟩ = some ⟨4,([false,false,true,true,true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),(rep [true,true,true,false,true] (n)) ++ ([true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,false,true,true] [] [false,false,false,true,true] [true,true,true,false,true] 7 local5 n (([true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true])) (([true,true,true,true]))

theorem phase6 (n : Nat) : run0 table 12 ⟨4,([false,false,true,true,true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),(rep [true,true,true,false,true] (n)) ++ ([true,true,true,true])⟩ = some ⟨1,([true]) ++ (rep [true] (n)) ++ ([true]),([false,true,true,true,true,true,true,true,false,true]) ++ (rep [true,true,true,false,true] (n)) ++ ([true,true,true,true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 1 ⟨1,([true]) ++ ([true]) ++ (L),(R)⟩ = some ⟨1,([true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (1*n) ⟨1,([true]) ++ (rep [true] (n)) ++ ([true]),([false,true,true,true,true,true,true,true,false,true]) ++ (rep [true,true,true,false,true] (n)) ++ ([true,true,true,true])⟩ = some ⟨1,([true,true]),(rep [true] (n)) ++ ([false,true,true,true,true,true,true,true,false,true]) ++ (rep [true,true,true,false,true] (n)) ++ ([true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true] [] [true] [true] 1 local7 n (([true])) (([false,true,true,true,true,true,true,true,false,true]) ++ (rep [true,true,true,false,true] (n)) ++ ([true,true,true,true]))

theorem phase8 (n : Nat) : run0 table 5 ⟨1,([true,true]),(rep [true] (n)) ++ ([false,true,true,true,true,true,true,true,false,true]) ++ (rep [true,true,true,false,true] (n)) ++ ([true,true,true,true])⟩ = some ⟨4,[],([true,true,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true,false,true]) ++ (rep [true,true,true,false,true] (n)) ++ ([true,true,true,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true,false,true]) ++ (rep [true,true,true,false,true] (n)) ++ ([true,true,true,true]) = ([true,true,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true,false,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true]) := by
  calc
    _ = ([true,true]) ++ (rep [true] (n)) ++ ([true,false,true,true,true,true,true,true,true,false,true]) ++ (rep [true,true,true,false,true] (n)) ++ ([true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true])) (([false,true,true,true,true,true,true,true,false,true]) ++ (rep [true,true,true,false,true] (n)) ++ ([true,true,true,true])) [] true n
    _ = ([true]) ++ (rep [true] (n)) ++ ([true,true,false,true,true,true,true,true,true,true,false,true]) ++ (rep [true,true,true,false,true] (n)) ++ ([true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true])) (([true,false,true,true,true,true,true,true,true,false,true]) ++ (rep [true,true,true,false,true] (n)) ++ ([true,true,true,true])) [] true n
    _ = (rep [true] (n)) ++ ([true,true,true,false,true,true,true,true,true,true,true,false,true]) ++ (rep [true,true,true,false,true] (n)) ++ ([true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,true,false,true,true,true,true,true,true,true,false,true]) ++ (rep [true,true,true,false,true] (n)) ++ ([true,true,true,true])) [] true n
    _ = (rep [true] (n)) ++ ([true,true,true,false,true,true,true,true,true,true,true,false,true,true]) ++ (rep [true,true,false,true,true] (n)) ++ ([true,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ((rep [true] (n)) ++ ([true,true,true,false,true,true,true,true,true,true,true,false,true])) (([true,true,true])) [true,true,false,true] true n
    _ = (rep [true] (n)) ++ ([true,true,true,false,true,true,true,true,true,true,true,false,true,true,true]) ++ (rep [true,false,true,true,true] (n)) ++ ([true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ((rep [true] (n)) ++ ([true,true,true,false,true,true,true,true,true,true,true,false,true,true])) (([true,true])) [true,false,true,true] true n
    _ = (rep [true] (n)) ++ ([true,true,true,false,true,true,true,true,true,true,true,false,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ((rep [true] (n)) ++ ([true,true,true,false,true,true,true,true,true,true,true,false,true,true,true])) (([true])) [false,true,true,true] true n
    _ = ([true]) ++ (rep [true] (n)) ++ ([true,true,false,true,true,true,true,true,true,true,false,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,true,false,true,true,true,true,true,true,true,false,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])) [] true n
    _ = ([true,true]) ++ (rep [true] (n)) ++ ([true,false,true,true,true,true,true,true,true,false,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true])) (([true,false,true,true,true,true,true,true,true,false,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])) [] true n
    _ = ([true,true,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true,false,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true])) (([false,true,true,true,true,true,true,true,false,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])) [] true n

theorem growth (n : Nat) : run0 table (84+32*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalR n] at H
  rw [show 3+7*n+31+17*n+33+7*n+12+1*n+5=84+32*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 48 (fun n => 84+32*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1087

namespace M1088

-- 1RB0RC_1RC1LE_0RD1LE_1LD0RA_1LF0LD_0LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,3⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([true,false,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true]) ++ (rep [false,true,false,true,true,true] (n)) ++ ([true,true])⟩

theorem entry : run0 table 506 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨4,[],([true,false,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true]) ++ (rep [false,true,false,true,true,true] (n)) ++ ([true,true])⟩ = some ⟨2,([false,false,false,false,true]),([true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true]) ++ (rep [false,true,false,true,true,true] (n)) ++ ([true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 50 ⟨2,([false]) ++ (L),([true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true]) ++ ([false,true,false,true,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,true,true]) ++ (L),([true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (50*n) ⟨2,([false,false,false,false,true]),([true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true]) ++ (rep [false,true,false,true,true,true] (n)) ++ ([true,true])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,true,true] (n)) ++ ([false,false,false,true]),([true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true] [false,true,false,true,true,true] [true,false,false,true,true,true] 50 local1 n (([false,false,false,true])) (([true,true]))

theorem phase2 (n : Nat) : run0 table 159 ⟨2,([false]) ++ (rep [true,false,false,true,true,true] (n)) ++ ([false,false,false,true]),([true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true,true,true])⟩ = some ⟨1,([true,true,false,false,false,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true]) ++ (rep [true,false,false,true,true,true] (n)) ++ ([false,false,false,true]),([false,true,true,true,true,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 14 ⟨1,([true,true,false,false,false,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true]) ++ ([true,false,false,true,true,true]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,false,false,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true]) ++ (L),([false,true,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (14*n) ⟨1,([true,true,false,false,false,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true]) ++ (rep [true,false,false,true,true,true] (n)) ++ ([false,false,false,true]),([false,true,true,true,true,true])⟩ = some ⟨1,([true,true,false,false,false,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true,false,false,false,true]),(rep [false,true,true,true,false,true] (n)) ++ ([false,true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,false,false,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true] [] [true,false,false,true,true,true] [false,true,true,true,false,true] 14 local3 n (([false,false,false,true])) (([false,true,true,true,true,true]))

theorem phase4 (n : Nat) : run0 table 75 ⟨1,([true,true,false,false,false,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true,false,false,false,true]),(rep [false,true,true,true,false,true] (n)) ++ ([false,true,true,true,true,true])⟩ = some ⟨4,[],([true,false,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true,false,true]) ++ (rep [false,true,true,true,false,true] (n)) ++ ([false,true,true,true,true,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true,false,true]) ++ (rep [false,true,true,true,false,true] (n)) ++ ([false,true,true,true,true,true]) = ([true,false,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true]) ++ (rep [false,true,false,true,true,true] (n)) ++ ([true,true]) := by
  calc
    _ = ([true,false,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true,false,true,false]) ++ (rep [true,true,true,false,true,false] (n)) ++ ([true,true,true,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true,false,true])) (([true,true,true,true,true])) [true,true,true,false,true] false n
    _ = ([true,false,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true]) ++ (rep [true,true,false,true,false,true] (n)) ++ ([true,true,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true,false,true,false])) (([true,true,true,true])) [true,true,false,true,false] true n
    _ = ([true,false,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true]) ++ (rep [true,false,true,false,true,true] (n)) ++ ([true,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true])) (([true,true,true])) [true,false,true,false,true] true n
    _ = ([true,false,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true]) ++ (rep [false,true,false,true,true,true] (n)) ++ ([true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true])) (([true,true])) [false,true,false,true,true] true n

theorem growth (n : Nat) : run0 table (240+64*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 6+50*n+159+14*n+75=240+64*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 506 (fun n => 240+64*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1088

namespace M1090

-- 1RB0RC_1RC1LE_0RD1LE_1LD0RA_1LF1LD_0LB---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,false,3⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([false,true,true,false,true,true]) ++ (rep [false,true,true,true,true,true] (n))⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 4 ⟨1,[],([false,true,true,false,true,true]) ++ (rep [false,true,true,true,true,true] (n))⟩ = some ⟨2,([false,false,false,false,true]),([true,true]) ++ (rep [false,true,true,true,true,true] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 24 ⟨2,([false]) ++ (L),([true,true]) ++ ([false,true,true,true,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,true,false,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (24*n) ⟨2,([false,false,false,false,true]),([true,true]) ++ (rep [false,true,true,true,true,true] (n))⟩ = some ⟨2,([false]) ++ (rep [true,true,true,false,false,false] (n)) ++ ([false,false,false,true]),([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true] [false,true,true,true,true,true] [true,true,true,false,false,false] 24 local1 n (([false,false,false,true])) ([])

theorem phase2 (n : Nat) : run0 table 6 ⟨2,([false]) ++ (rep [true,true,true,false,false,false] (n)) ++ ([false,false,false,true]),([true,true])⟩ = some ⟨3,([false,false,false]) ++ (rep [true,true,true,false,false,false] (n)) ++ ([false,false,false,true]),([true,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 10 ⟨3,([false,false,false]) ++ ([true,true,true,false,false,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,false]) ++ (L),([true,true,false,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (10*n) ⟨3,([false,false,false]) ++ (rep [true,true,true,false,false,false] (n)) ++ ([false,false,false,true]),([true,true])⟩ = some ⟨3,([false,false,false,false,false,false,true]),(rep [true,true,false,true,true,true] (n)) ++ ([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false] [] [true,true,true,false,false,false] [true,true,false,true,true,true] 10 local3 n (([false,false,false,true])) (([true,true]))

theorem phase4 (n : Nat) : run0 table 33 ⟨3,([false,false,false,false,false,false,true]),(rep [true,true,false,true,true,true] (n)) ++ ([true,true])⟩ = some ⟨2,([false,true,true,true,true]),([true,true,true]) ++ (rep [true,true,false,true,true,true] (n)) ++ ([true,true])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 24 ⟨2,([false]) ++ (L),([true,true,true]) ++ ([true,true,false,true,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([false,false,false,true,true,true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (24*n) ⟨2,([false,true,true,true,true]),([true,true,true]) ++ (rep [true,true,false,true,true,true] (n)) ++ ([true,true])⟩ = some ⟨2,([false]) ++ (rep [false,false,false,true,true,true] (n)) ++ ([true,true,true,true]),([true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,true] [true,true,false,true,true,true] [false,false,false,true,true,true] 24 local5 n (([true,true,true,true])) (([true,true]))

theorem phase6 (n : Nat) : run0 table 27 ⟨2,([false]) ++ (rep [false,false,false,true,true,true] (n)) ++ ([true,true,true,true]),([true,true,true,true,true])⟩ = some ⟨3,([false,false,false,true,true,true]) ++ (rep [false,false,false,true,true,true] (n)) ++ ([true,true,true,true]),([true,true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 10 ⟨3,([false,false,false,true,true,true]) ++ ([false,false,false,true,true,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,true,true,true]) ++ (L),([true,true,false,true,true,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (10*n) ⟨3,([false,false,false,true,true,true]) ++ (rep [false,false,false,true,true,true] (n)) ++ ([true,true,true,true]),([true,true])⟩ = some ⟨3,([false,false,false,true,true,true,true,true,true,true]),(rep [true,true,false,true,true,true] (n)) ++ ([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,true,true,true] [] [false,false,false,true,true,true] [true,true,false,true,true,true] 10 local7 n (([true,true,true,true])) (([true,true]))

theorem phase8 (n : Nat) : run0 table 22 ⟨3,([false,false,false,true,true,true,true,true,true,true]),(rep [true,true,false,true,true,true] (n)) ++ ([true,true])⟩ = some ⟨1,[],([false,true,true,false,true,true,false,true,true,true]) ++ (rep [true,true,false,true,true,true] (n)) ++ ([true,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,true,true,false,true,true,false,true,true,true]) ++ (rep [true,true,false,true,true,true] (n)) ++ ([true,true]) = ([false,true,true,false,true,true,false,true,true,true,true,true]) ++ (rep [false,true,true,true,true,true] (n)) := by
  calc
    _ = ([false,true,true,false,true,true,false,true,true,true,true]) ++ (rep [true,false,true,true,true,true] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,true,false,true,true,true])) (([true])) [true,false,true,true,true] true n
    _ = ([false,true,true,false,true,true,false,true,true,true,true,true]) ++ (rep [false,true,true,true,true,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,true,false,true,true,true,true])) ([]) [false,true,true,true,true] true n

theorem growth (n : Nat) : run0 table (92+68*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalR n] at H
  rw [show 4+24*n+6+10*n+33+24*n+27+10*n+22=92+68*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 92+68*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1090

namespace M1387

-- 1RB0RC_1RC0LF_0RD1LF_1LD0RA_0LB---_1LE0RD

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,true,3⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([false,false,true,true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩

theorem entry : run0 table 11 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 9 ⟨5,[],([false,false,true,true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ = some ⟨3,([true,false,true,false,false,true]),([true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 72 ⟨3,([true]) ++ (L),([true]) ++ ([false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (72*n) ⟨3,([true,false,true,false,false,true]),([true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ = some ⟨3,([true]) ++ (rep [false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false] (n)) ++ ([false,true,false,false,true]),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true] [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] [false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false] 72 local1 n (([false,true,false,false,true])) ([])

theorem phase2 (n : Nat) : run0 table 3 ⟨3,([true]) ++ (rep [false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false] (n)) ++ ([false,true,false,false,true]),([true])⟩ = some ⟨3,([false,false,false,false]) ++ (rep [false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false] (n)) ++ ([false,true,false,false,true]),[]⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 36 ⟨3,([false,false,false,false]) ++ ([false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,false]) ++ (L),([false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (36*n) ⟨3,([false,false,false,false]) ++ (rep [false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false] (n)) ++ ([false,true,false,false,true]),[]⟩ = some ⟨3,([false,false,false,false,false,true,false,false,true]),(rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,false] [] [false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false] [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] 36 local3 n (([false,true,false,false,true])) ([])

theorem phase4 (n : Nat) : run0 table 11 ⟨3,([false,false,false,false,false,true,false,false,true]),(rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ = some ⟨2,([false,true,false,true]),([true,true,true,true,true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 72 ⟨2,([false]) ++ (L),([true,true,true,true,true]) ++ ([false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true]) ++ (L),([true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (72*n) ⟨2,([false,true,false,true]),([true,true,true,true,true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ = some ⟨2,([false]) ++ (rep [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] (n)) ++ ([true,false,true]),([true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,true,true,true] [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] 72 local5 n (([true,false,true])) ([])

theorem phase6 (n : Nat) : run0 table 25 ⟨2,([false]) ++ (rep [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] (n)) ++ ([true,false,true]),([true,true,true,true,true])⟩ = some ⟨3,([false,false,false,false,false,true,true,true]) ++ (rep [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] (n)) ++ ([true,false,true]),[]⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 36 ⟨3,([false,false,false,false,false,true,true,true]) ++ ([false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,false,false,true,true,true]) ++ (L),([false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (36*n) ⟨3,([false,false,false,false,false,true,true,true]) ++ (rep [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] (n)) ++ ([true,false,true]),[]⟩ = some ⟨3,([false,false,false,false,false,true,true,true,true,false,true]),(rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,false,false,true,true,true] [] [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] 36 local7 n (([true,false,true])) ([])

theorem phase8 (n : Nat) : run0 table 14 ⟨3,([false,false,false,false,false,true,true,true,true,false,true]),(rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ = some ⟨3,([true,false,true]),([true,true,false,true,true,true,true,true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ := by rfl

theorem local9 (L R : List Bool) : run0 table 72 ⟨3,([true,false]) ++ (L),([true,true,false,true,true,true,true,true]) ++ ([false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (R)⟩ = some ⟨3,([true,false]) ++ ([true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true]) ++ (L),([true,true,false,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase9 (n : Nat) : run0 table (72*n) ⟨3,([true,false,true]),([true,true,false,true,true,true,true,true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ = some ⟨3,([true,false]) ++ (rep [true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true] (n)) ++ ([true]),([true,true,false,true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true,false] [true,true,false,true,true,true,true,true] [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] [true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true] 72 local9 n (([true])) ([])

theorem phase10 (n : Nat) : run0 table 34 ⟨3,([true,false]) ++ (rep [true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true] (n)) ++ ([true]),([true,true,false,true,true,true,true,true])⟩ = some ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true]) ++ (rep [true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true] (n)) ++ ([true]),[]⟩ := by rfl

theorem local11 (L R : List Bool) : run0 table 36 ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true]) ++ ([true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true]) ++ (L),([false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase11 (n : Nat) : run0 table (36*n) ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true]) ++ (rep [true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true] (n)) ++ ([true]),[]⟩ = some ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true]),(rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,false,false,true,true,true,false,false,false,true] [] [true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true] [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] 36 local11 n (([true])) ([])

theorem phase12 (n : Nat) : run0 table 32 ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true]),(rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ = some ⟨3,([true,false,true,false,false,true]),([true,true,true,true,false,true,true,true,true,true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ := by rfl

theorem local13 (L R : List Bool) : run0 table 72 ⟨3,([true,false]) ++ (L),([true,true,true,true,false,true,true,true,true,true]) ++ ([false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (R)⟩ = some ⟨3,([true,false]) ++ ([false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true]) ++ (L),([true,true,true,true,false,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase13 (n : Nat) : run0 table (72*n) ⟨3,([true,false,true,false,false,true]),([true,true,true,true,false,true,true,true,true,true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ = some ⟨3,([true,false]) ++ (rep [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] (n)) ++ ([true,false,false,true]),([true,true,true,true,false,true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true,false] [true,true,true,true,false,true,true,true,true,true] [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] 72 local13 n (([true,false,false,true])) ([])

theorem phase14 (n : Nat) : run0 table 48 ⟨3,([true,false]) ++ (rep [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] (n)) ++ ([true,false,false,true]),([true,true,true,true,false,true,true,true,true,true])⟩ = some ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true]) ++ (rep [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] (n)) ++ ([true,false,false,true]),[]⟩ := by rfl

theorem local15 (L R : List Bool) : run0 table 36 ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true]) ++ ([false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true]) ++ (L),([false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase15 (n : Nat) : run0 table (36*n) ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true]) ++ (rep [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] (n)) ++ ([true,false,false,true]),[]⟩ = some ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true,true,false,false,true]),(rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,false,false,true,true,true,false,false,false,true,true,true] [] [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] 36 local15 n (([true,false,false,true])) ([])

theorem phase16 (n : Nat) : run0 table 26 ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true,true,false,false,true]),(rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ = some ⟨3,([true,false,false,true]),([true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ := by rfl

theorem local17 (L R : List Bool) : run0 table 72 ⟨3,([true,false]) ++ (L),([true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ ([false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (R)⟩ = some ⟨3,([true,false]) ++ ([true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true]) ++ (L),([true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase17 (n : Nat) : run0 table (72*n) ⟨3,([true,false,false,true]),([true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ = some ⟨3,([true,false]) ++ (rep [true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true] (n)) ++ ([false,true]),([true,true,false,true,true,true,true,true,false,true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true,false] [true,true,false,true,true,true,true,true,false,true,true,true,true,true] [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] [true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true] 72 local17 n (([false,true])) ([])

theorem phase18 (n : Nat) : run0 table 58 ⟨3,([true,false]) ++ (rep [true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true] (n)) ++ ([false,true]),([true,true,false,true,true,true,true,true,false,true,true,true,true,true])⟩ = some ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true]) ++ (rep [true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true] (n)) ++ ([false,true]),[]⟩ := by rfl

theorem local19 (L R : List Bool) : run0 table 36 ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true]) ++ ([true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true]) ++ (L),([false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase19 (n : Nat) : run0 table (36*n) ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true]) ++ (rep [true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true] (n)) ++ ([false,true]),[]⟩ = some ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,false,true]),(rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true] [] [true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true] [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] 36 local19 n (([false,true])) ([])

theorem phase20 (n : Nat) : run0 table 35 ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,false,true]),(rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ = some ⟨2,([false,true,true]),([true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ := by rfl

theorem local21 (L R : List Bool) : run0 table 72 ⟨2,([false]) ++ (L),([true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ ([false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true]) ++ (L),([true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase21 (n : Nat) : run0 table (72*n) ⟨2,([false,true,true]),([true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ = some ⟨2,([false]) ++ (rep [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] (n)) ++ ([true,true]),([true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] 72 local21 n (([true,true])) ([])

theorem phase22 (n : Nat) : run0 table 73 ⟨2,([false]) ++ (rep [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] (n)) ++ ([true,true]),([true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true])⟩ = some ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true]) ++ (rep [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] (n)) ++ ([true,true]),[]⟩ := by rfl

theorem local23 (L R : List Bool) : run0 table 36 ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true]) ++ ([false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true]) ++ (L),([false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase23 (n : Nat) : run0 table (36*n) ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true]) ++ (rep [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] (n)) ++ ([true,true]),[]⟩ = some ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,true,true]),(rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] [] [false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true] [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] 36 local23 n (([true,true])) ([])

theorem phase24 (n : Nat) : run0 table 44 ⟨3,([false,false,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,true,true]),(rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ = some ⟨5,[],([false,false,true,true,false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,false,true,true,false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n)) = ([false,false,true,true,false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true]) ++ (rep [false,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true] (n)) := by
  rfl

theorem growth (n : Nat) : run0 table (412+648*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n)) (phase9 n)) (phase10 n)) (phase11 n)) (phase12 n)) (phase13 n)) (phase14 n)) (phase15 n)) (phase16 n)) (phase17 n)) (phase18 n)) (phase19 n)) (phase20 n)) (phase21 n)) (phase22 n)) (phase23 n)) (phase24 n))
  rw [show 9+72*n+3+36*n+11+72*n+25+36*n+14+72*n+34+36*n+32+72*n+48+36*n+26+72*n+58+36*n+35+72*n+73+36*n+44=412+648*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 11 (fun n => 412+648*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1387

namespace M1391

-- 1RB0RC_1RC1LB_0RD1LF_1LD0RA_0LB---_1LE0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨4,[],([false,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩

theorem entry : run0 table 56 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 11 ⟨4,[],([false,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨2,([false,true]),([true,true,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 7 ⟨2,([false]) ++ (L),([true,true,true]) ++ ([true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (7*n) ⟨2,([false,true]),([true,true,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨2,([false]) ++ (rep [true] (n)) ++ ([true]),([true,true,true,false,true,true,true,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,true] [true] [true] 7 local1 n (([true])) (([false,true,true,true,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true]))

theorem phase2 (n : Nat) : run0 table 31 ⟨2,([false]) ++ (rep [true] (n)) ++ ([true]),([true,true,true,false,true,true,true,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨2,([false,true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 17 ⟨2,([false]) ++ (L),([true,true,true,true]) ++ ([false,true,true,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([false,false,false,true,true]) ++ (L),([true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (17*n) ⟨2,([false,true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨2,([false]) ++ (rep [false,false,false,true,true] (n)) ++ ([true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,true,true] [false,true,true,true,true] [false,false,false,true,true] 17 local3 n (([true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true])) (([true]))

theorem phase4 (n : Nat) : run0 table 28 ⟨2,([false]) ++ (rep [false,false,false,true,true] (n)) ++ ([true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true,true,true,true,true])⟩ = some ⟨3,([false,false,true,true,true]) ++ (rep [false,false,false,true,true] (n)) ++ ([true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true,true,true])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 15 ⟨3,([false,false,true,true,true]) ++ ([false,false,false,true,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,true,true,true]) ++ (L),([true,true,false,true,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (15*n) ⟨3,([false,false,true,true,true]) ++ (rep [false,false,false,true,true] (n)) ++ ([true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true,true,true])⟩ = some ⟨3,([false,false,true,true,true,true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),(rep [true,true,false,true,true] (n)) ++ ([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,true,true,true] [] [false,false,false,true,true] [true,true,false,true,true] 15 local5 n (([true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true])) (([true,true,true]))

theorem phase6 (n : Nat) : run0 table 25 ⟨3,([false,false,true,true,true,true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),(rep [true,true,false,true,true] (n)) ++ ([true,true,true])⟩ = some ⟨1,([true]) ++ (rep [true] (n)) ++ ([true]),([false,true,true,true,true,true,true,true,false,true,true]) ++ (rep [true,true,false,true,true] (n)) ++ ([true,true,true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 1 ⟨1,([true]) ++ ([true]) ++ (L),(R)⟩ = some ⟨1,([true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (1*n) ⟨1,([true]) ++ (rep [true] (n)) ++ ([true]),([false,true,true,true,true,true,true,true,false,true,true]) ++ (rep [true,true,false,true,true] (n)) ++ ([true,true,true])⟩ = some ⟨1,([true,true]),(rep [true] (n)) ++ ([false,true,true,true,true,true,true,true,false,true,true]) ++ (rep [true,true,false,true,true] (n)) ++ ([true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true] [] [true] [true] 1 local7 n (([true])) (([false,true,true,true,true,true,true,true,false,true,true]) ++ (rep [true,true,false,true,true] (n)) ++ ([true,true,true]))

theorem phase8 (n : Nat) : run0 table 5 ⟨1,([true,true]),(rep [true] (n)) ++ ([false,true,true,true,true,true,true,true,false,true,true]) ++ (rep [true,true,false,true,true] (n)) ++ ([true,true,true])⟩ = some ⟨4,[],([false,true,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true,false,true,true]) ++ (rep [true,true,false,true,true] (n)) ++ ([true,true,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,true,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true,false,true,true]) ++ (rep [true,true,false,true,true] (n)) ++ ([true,true,true]) = ([false,true,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true,false,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true]) := by
  calc
    _ = ([false,true]) ++ (rep [true] (n)) ++ ([true,false,true,true,true,true,true,true,true,false,true,true]) ++ (rep [true,true,false,true,true] (n)) ++ ([true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([false,true,true,true,true,true,true,true,false,true,true]) ++ (rep [true,true,false,true,true] (n)) ++ ([true,true,true])) [] true n
    _ = ([false]) ++ (rep [true] (n)) ++ ([true,true,false,true,true,true,true,true,true,true,false,true,true]) ++ (rep [true,true,false,true,true] (n)) ++ ([true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([true,false,true,true,true,true,true,true,true,false,true,true]) ++ (rep [true,true,false,true,true] (n)) ++ ([true,true,true])) [] true n
    _ = ([false]) ++ (rep [true] (n)) ++ ([true,true,false,true,true,true,true,true,true,true,false,true,true,true]) ++ (rep [true,false,true,true,true] (n)) ++ ([true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false]) ++ (rep [true] (n)) ++ ([true,true,false,true,true,true,true,true,true,true,false,true,true])) (([true,true])) [true,false,true,true] true n
    _ = ([false]) ++ (rep [true] (n)) ++ ([true,true,false,true,true,true,true,true,true,true,false,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false]) ++ (rep [true] (n)) ++ ([true,true,false,true,true,true,true,true,true,true,false,true,true,true])) (([true])) [false,true,true,true] true n
    _ = ([false,true]) ++ (rep [true] (n)) ++ ([true,false,true,true,true,true,true,true,true,false,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([true,false,true,true,true,true,true,true,true,false,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])) [] true n
    _ = ([false,true,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true,false,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([false,true,true,true,true,true,true,true,false,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])) [] true n

theorem growth (n : Nat) : run0 table (100+40*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalR n] at H
  rw [show 11+7*n+31+17*n+28+15*n+25+1*n+5=100+40*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 56 (fun n => 100+40*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1391

namespace M1392

-- 1RB0RC_1RC1LB_0RD1LF_1LD0RA_0LB---_1LE1LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([true,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩

theorem entry : run0 table 48 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 3 ⟨5,[],([true,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨2,([false,true]),([true,true,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 7 ⟨2,([false]) ++ (L),([true,true,true]) ++ ([true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (7*n) ⟨2,([false,true]),([true,true,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨2,([false]) ++ (rep [true] (n)) ++ ([true]),([true,true,true,false,true,true,true,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,true] [true] [true] 7 local1 n (([true])) (([false,true,true,true,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true]))

theorem phase2 (n : Nat) : run0 table 31 ⟨2,([false]) ++ (rep [true] (n)) ++ ([true]),([true,true,true,false,true,true,true,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨2,([false,true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 17 ⟨2,([false]) ++ (L),([true,true,true,true]) ++ ([false,true,true,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([false,false,false,true,true]) ++ (L),([true,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (17*n) ⟨2,([false,true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])⟩ = some ⟨2,([false]) ++ (rep [false,false,false,true,true] (n)) ++ ([true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,true,true] [false,true,true,true,true] [false,false,false,true,true] 17 local3 n (([true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true])) (([true]))

theorem phase4 (n : Nat) : run0 table 33 ⟨2,([false]) ++ (rep [false,false,false,true,true] (n)) ++ ([true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true,true,true,true,true])⟩ = some ⟨5,([false,false,true,true]) ++ (rep [false,false,false,true,true] (n)) ++ ([true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true,true,true,true])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 7 ⟨5,([false,false,true,true]) ++ ([false,false,false,true,true]) ++ (L),(R)⟩ = some ⟨5,([false,false,true,true]) ++ (L),([true,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (7*n) ⟨5,([false,false,true,true]) ++ (rep [false,false,false,true,true] (n)) ++ ([true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),([true,true,true,true])⟩ = some ⟨5,([false,false,true,true,true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),(rep [true,true,true,false,true] (n)) ++ ([true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,true,true] [] [false,false,false,true,true] [true,true,true,false,true] 7 local5 n (([true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true])) (([true,true,true,true]))

theorem phase6 (n : Nat) : run0 table 12 ⟨5,([false,false,true,true,true,true,true,false,false,false,true]) ++ (rep [true] (n)) ++ ([true]),(rep [true,true,true,false,true] (n)) ++ ([true,true,true,true])⟩ = some ⟨1,([true]) ++ (rep [true] (n)) ++ ([true]),([false,true,true,true,true,true,true,true,false,true]) ++ (rep [true,true,true,false,true] (n)) ++ ([true,true,true,true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 1 ⟨1,([true]) ++ ([true]) ++ (L),(R)⟩ = some ⟨1,([true]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (1*n) ⟨1,([true]) ++ (rep [true] (n)) ++ ([true]),([false,true,true,true,true,true,true,true,false,true]) ++ (rep [true,true,true,false,true] (n)) ++ ([true,true,true,true])⟩ = some ⟨1,([true,true]),(rep [true] (n)) ++ ([false,true,true,true,true,true,true,true,false,true]) ++ (rep [true,true,true,false,true] (n)) ++ ([true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true] [] [true] [true] 1 local7 n (([true])) (([false,true,true,true,true,true,true,true,false,true]) ++ (rep [true,true,true,false,true] (n)) ++ ([true,true,true,true]))

theorem phase8 (n : Nat) : run0 table 5 ⟨1,([true,true]),(rep [true] (n)) ++ ([false,true,true,true,true,true,true,true,false,true]) ++ (rep [true,true,true,false,true] (n)) ++ ([true,true,true,true])⟩ = some ⟨5,[],([true,true,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true,false,true]) ++ (rep [true,true,true,false,true] (n)) ++ ([true,true,true,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,true,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true,false,true]) ++ (rep [true,true,true,false,true] (n)) ++ ([true,true,true,true]) = ([true,true,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true,false,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true]) := by
  calc
    _ = ([true,true]) ++ (rep [true] (n)) ++ ([true,false,true,true,true,true,true,true,true,false,true]) ++ (rep [true,true,true,false,true] (n)) ++ ([true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true])) (([false,true,true,true,true,true,true,true,false,true]) ++ (rep [true,true,true,false,true] (n)) ++ ([true,true,true,true])) [] true n
    _ = ([true]) ++ (rep [true] (n)) ++ ([true,true,false,true,true,true,true,true,true,true,false,true]) ++ (rep [true,true,true,false,true] (n)) ++ ([true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true])) (([true,false,true,true,true,true,true,true,true,false,true]) ++ (rep [true,true,true,false,true] (n)) ++ ([true,true,true,true])) [] true n
    _ = (rep [true] (n)) ++ ([true,true,true,false,true,true,true,true,true,true,true,false,true]) ++ (rep [true,true,true,false,true] (n)) ++ ([true,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,true,false,true,true,true,true,true,true,true,false,true]) ++ (rep [true,true,true,false,true] (n)) ++ ([true,true,true,true])) [] true n
    _ = (rep [true] (n)) ++ ([true,true,true,false,true,true,true,true,true,true,true,false,true,true]) ++ (rep [true,true,false,true,true] (n)) ++ ([true,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ((rep [true] (n)) ++ ([true,true,true,false,true,true,true,true,true,true,true,false,true])) (([true,true,true])) [true,true,false,true] true n
    _ = (rep [true] (n)) ++ ([true,true,true,false,true,true,true,true,true,true,true,false,true,true,true]) ++ (rep [true,false,true,true,true] (n)) ++ ([true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ((rep [true] (n)) ++ ([true,true,true,false,true,true,true,true,true,true,true,false,true,true])) (([true,true])) [true,false,true,true] true n
    _ = (rep [true] (n)) ++ ([true,true,true,false,true,true,true,true,true,true,true,false,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ((rep [true] (n)) ++ ([true,true,true,false,true,true,true,true,true,true,true,false,true,true,true])) (([true])) [false,true,true,true] true n
    _ = ([true]) ++ (rep [true] (n)) ++ ([true,true,false,true,true,true,true,true,true,true,false,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,true,false,true,true,true,true,true,true,true,false,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])) [] true n
    _ = ([true,true]) ++ (rep [true] (n)) ++ ([true,false,true,true,true,true,true,true,true,false,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true])) (([true,false,true,true,true,true,true,true,true,false,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])) [] true n
    _ = ([true,true,true]) ++ (rep [true] (n)) ++ ([false,true,true,true,true,true,true,true,false,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true])) (([false,true,true,true,true,true,true,true,false,true,true,true,true]) ++ (rep [false,true,true,true,true] (n)) ++ ([true])) [] true n

theorem growth (n : Nat) : run0 table (84+32*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalR n] at H
  rw [show 3+7*n+31+17*n+33+7*n+12+1*n+5=84+32*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 48 (fun n => 84+32*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1392

namespace M1398

-- 1RB0RC_1RC1LF_0RD1LF_1LD0RA_0LB---_1LE0LD

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[],([true,false,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true]) ++ (rep [false,true,false,true,true,true] (n)) ++ ([true,true])⟩

theorem entry : run0 table 506 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 6 ⟨5,[],([true,false,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true]) ++ (rep [false,true,false,true,true,true] (n)) ++ ([true,true])⟩ = some ⟨2,([false,false,false,false,true]),([true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true]) ++ (rep [false,true,false,true,true,true] (n)) ++ ([true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 50 ⟨2,([false]) ++ (L),([true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true]) ++ ([false,true,false,true,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,false,false,true,true,true]) ++ (L),([true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (50*n) ⟨2,([false,false,false,false,true]),([true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true]) ++ (rep [false,true,false,true,true,true] (n)) ++ ([true,true])⟩ = some ⟨2,([false]) ++ (rep [true,false,false,true,true,true] (n)) ++ ([false,false,false,true]),([true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true] [false,true,false,true,true,true] [true,false,false,true,true,true] 50 local1 n (([false,false,false,true])) (([true,true]))

theorem phase2 (n : Nat) : run0 table 159 ⟨2,([false]) ++ (rep [true,false,false,true,true,true] (n)) ++ ([false,false,false,true]),([true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true,true,true])⟩ = some ⟨1,([true,true,false,false,false,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true]) ++ (rep [true,false,false,true,true,true] (n)) ++ ([false,false,false,true]),([false,true,true,true,true,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 14 ⟨1,([true,true,false,false,false,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true]) ++ ([true,false,false,true,true,true]) ++ (L),(R)⟩ = some ⟨1,([true,true,false,false,false,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true]) ++ (L),([false,true,true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (14*n) ⟨1,([true,true,false,false,false,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true]) ++ (rep [true,false,false,true,true,true] (n)) ++ ([false,false,false,true]),([false,true,true,true,true,true])⟩ = some ⟨1,([true,true,false,false,false,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true,false,false,false,true]),(rep [false,true,true,true,false,true] (n)) ++ ([false,true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,false,false,false,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true] [] [true,false,false,true,true,true] [false,true,true,true,false,true] 14 local3 n (([false,false,false,true])) (([false,true,true,true,true,true]))

theorem phase4 (n : Nat) : run0 table 75 ⟨1,([true,true,false,false,false,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true,false,false,false,true]),(rep [false,true,true,true,false,true] (n)) ++ ([false,true,true,true,true,true])⟩ = some ⟨5,[],([true,false,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true,false,true]) ++ (rep [false,true,true,true,false,true] (n)) ++ ([false,true,true,true,true,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true,false,true]) ++ (rep [false,true,true,true,false,true] (n)) ++ ([false,true,true,true,true,true]) = ([true,false,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true]) ++ (rep [false,true,false,true,true,true] (n)) ++ ([true,true]) := by
  calc
    _ = ([true,false,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true,false,true,false]) ++ (rep [true,true,true,false,true,false] (n)) ++ ([true,true,true,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true,false,true])) (([true,true,true,true,true])) [true,true,true,false,true] false n
    _ = ([true,false,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true]) ++ (rep [true,true,false,true,false,true] (n)) ++ ([true,true,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true,false,true,false])) (([true,true,true,true])) [true,true,false,true,false] true n
    _ = ([true,false,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true]) ++ (rep [true,false,true,false,true,true] (n)) ++ ([true,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true])) (([true,true,true])) [true,false,true,false,true] true n
    _ = ([true,false,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true]) ++ (rep [false,true,false,true,true,true] (n)) ++ ([true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,true,true,true,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true,false,true,false,true,true])) (([true,true])) [false,true,false,true,true] true n

theorem growth (n : Nat) : run0 table (240+64*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 6+50*n+159+14*n+75=240+64*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 506 (fun n => 240+64*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1398

namespace M1400

-- 1RB0RC_1RC1LF_0RD1LF_1LD0RA_0LB---_1LE1LD

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨true,false,3⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],([false,true,true,false,true,true]) ++ (rep [false,true,true,true,true,true] (n))⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem phase0 (n : Nat) : run0 table 4 ⟨1,[],([false,true,true,false,true,true]) ++ (rep [false,true,true,true,true,true] (n))⟩ = some ⟨2,([false,false,false,false,true]),([true,true]) ++ (rep [false,true,true,true,true,true] (n))⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 24 ⟨2,([false]) ++ (L),([true,true]) ++ ([false,true,true,true,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([true,true,true,false,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (24*n) ⟨2,([false,false,false,false,true]),([true,true]) ++ (rep [false,true,true,true,true,true] (n))⟩ = some ⟨2,([false]) ++ (rep [true,true,true,false,false,false] (n)) ++ ([false,false,false,true]),([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true] [false,true,true,true,true,true] [true,true,true,false,false,false] 24 local1 n (([false,false,false,true])) ([])

theorem phase2 (n : Nat) : run0 table 6 ⟨2,([false]) ++ (rep [true,true,true,false,false,false] (n)) ++ ([false,false,false,true]),([true,true])⟩ = some ⟨3,([false,false,false]) ++ (rep [true,true,true,false,false,false] (n)) ++ ([false,false,false,true]),([true,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 10 ⟨3,([false,false,false]) ++ ([true,true,true,false,false,false]) ++ (L),(R)⟩ = some ⟨3,([false,false,false]) ++ (L),([true,true,false,true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (10*n) ⟨3,([false,false,false]) ++ (rep [true,true,true,false,false,false] (n)) ++ ([false,false,false,true]),([true,true])⟩ = some ⟨3,([false,false,false,false,false,false,true]),(rep [true,true,false,true,true,true] (n)) ++ ([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false] [] [true,true,true,false,false,false] [true,true,false,true,true,true] 10 local3 n (([false,false,false,true])) (([true,true]))

theorem phase4 (n : Nat) : run0 table 33 ⟨3,([false,false,false,false,false,false,true]),(rep [true,true,false,true,true,true] (n)) ++ ([true,true])⟩ = some ⟨2,([false,true,true,true,true]),([true,true,true]) ++ (rep [true,true,false,true,true,true] (n)) ++ ([true,true])⟩ := by rfl

theorem local5 (L R : List Bool) : run0 table 24 ⟨2,([false]) ++ (L),([true,true,true]) ++ ([true,true,false,true,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([false,false,false,true,true,true]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase5 (n : Nat) : run0 table (24*n) ⟨2,([false,true,true,true,true]),([true,true,true]) ++ (rep [true,true,false,true,true,true] (n)) ++ ([true,true])⟩ = some ⟨2,([false]) ++ (rep [false,false,false,true,true,true] (n)) ++ ([true,true,true,true]),([true,true,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,true] [true,true,false,true,true,true] [false,false,false,true,true,true] 24 local5 n (([true,true,true,true])) (([true,true]))

theorem phase6 (n : Nat) : run0 table 27 ⟨2,([false]) ++ (rep [false,false,false,true,true,true] (n)) ++ ([true,true,true,true]),([true,true,true,true,true])⟩ = some ⟨3,([false,false,false,true,true,true]) ++ (rep [false,false,false,true,true,true] (n)) ++ ([true,true,true,true]),([true,true])⟩ := by rfl

theorem local7 (L R : List Bool) : run0 table 10 ⟨3,([false,false,false,true,true,true]) ++ ([false,false,false,true,true,true]) ++ (L),(R)⟩ = some ⟨3,([false,false,false,true,true,true]) ++ (L),([true,true,false,true,true,true]) ++ (R)⟩ := by rfl

theorem phase7 (n : Nat) : run0 table (10*n) ⟨3,([false,false,false,true,true,true]) ++ (rep [false,false,false,true,true,true] (n)) ++ ([true,true,true,true]),([true,true])⟩ = some ⟨3,([false,false,false,true,true,true,true,true,true,true]),(rep [true,true,false,true,true,true] (n)) ++ ([true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [false,false,false,true,true,true] [] [false,false,false,true,true,true] [true,true,false,true,true,true] 10 local7 n (([true,true,true,true])) (([true,true]))

theorem phase8 (n : Nat) : run0 table 22 ⟨3,([false,false,false,true,true,true,true,true,true,true]),(rep [true,true,false,true,true,true] (n)) ++ ([true,true])⟩ = some ⟨1,[],([false,true,true,false,true,true,false,true,true,true]) ++ (rep [true,true,false,true,true,true] (n)) ++ ([true,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([false,true,true,false,true,true,false,true,true,true]) ++ (rep [true,true,false,true,true,true] (n)) ++ ([true,true]) = ([false,true,true,false,true,true,false,true,true,true,true,true]) ++ (rep [false,true,true,true,true,true] (n)) := by
  calc
    _ = ([false,true,true,false,true,true,false,true,true,true,true]) ++ (rep [true,false,true,true,true,true] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,true,false,true,true,true])) (([true])) [true,false,true,true,true] true n
    _ = ([false,true,true,false,true,true,false,true,true,true,true,true]) ++ (rep [false,true,true,true,true,true] (n)) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,true,false,true,true,true,true])) ([]) [false,true,true,true,true] true n

theorem growth (n : Nat) : run0 table (92+68*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n)) (phase5 n)) (phase6 n)) (phase7 n)) (phase8 n))
  rw [finalR n] at H
  rw [show 4+24*n+6+10*n+33+24*n+27+10*n+22=92+68*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 92+68*n) entry (by intro n; omega) growth m hm

#print axioms never

end M1400

end BB6.Agent11Raw39RCPumps
