import Raw39CounterCarry
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent11CounterCarry
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39RCCounter107
namespace M107

namespace MInit

-- 1RB0RC_1RC1LE_0RD0LF_1LD0RA_1LA0LB_0LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 5 ⟨4,[],(rep [true,false,true] (n)) ++ ([true,false,true,false,false,false,false])⟩ = some ⟨2,([false,true]),([true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,false,false,false,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨2,([false]) ++ (L),([true]) ++ ([true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([false,false,false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨2,([false,true]),([true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,false,false,false,false])⟩ = some ⟨2,([false]) ++ (rep [false,false,false] (n)) ++ ([true]),([true,true,false,true,false,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true] [true,false,true] [false,false,false] 3 local1 n (([true])) (([true,false,true,false,false,false,false]))

theorem phase2 (n : Nat) : run0 table 3 ⟨2,([false]) ++ (rep [false,false,false] (n)) ++ ([true]),([true,true,false,true,false,false,false,false])⟩ = some ⟨2,([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]),([true,false,false,false,false])⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]) = (rep [false,false,false] (n)) ++ ([false,false,false,false,true]) := by
  calc
    _ = ([false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false])) (([true])) [false,false] false n
    _ = ([false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,true])) [false,false] false n
    _ = ([false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,true])) [false,false] false n
    _ = (rep [false,false,false] (n)) ++ ([false,false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,false,false,true])) [false,false] false n

theorem finalR (n : Nat) : ([true,false,false,false,false]) = ([true,false,false,false,false]) := by
  rfl

theorem epoch (n : Nat) : run0 table (8+3*n) ⟨4,[],(rep [true,false,true] (n)) ++ ([true,false,true,false,false,false,false])⟩ = some ⟨2,(rep [false,false,false] (n)) ++ ([false,false,false,false,true]),([true,false,false,false,false])⟩ := by
  have H := (join0 (join0 (phase0 n) (phase1 n)) (phase2 n))
  rw [finalL n] at H
  rw [show 5+3*n+3=8+3*n by omega] at H
  exact H

theorem canon (n : Nat) : run0 table (8+3*n) ⟨4,[],(rep [true,false,true] (n)) ++ ([true,false,true,false,false,false,false])⟩ = some ⟨2,(rep [false,false,false] (n)) ++ ([false,false,false,false,true]),([true,false,false,false,false])⟩ := by
  exact epoch n

end MInit


namespace MFinish

-- 1RB0RC_1RC1LE_0RD0LF_1LD0RA_1LA0LB_0LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 15 ⟨2,([false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false,true]),([true,false,false,false,false])⟩ = some ⟨4,([false,false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false,true]),([false,false,false,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 5 ⟨4,([false,false,true,false]) ++ ([false,true,false]) ++ (L),(R)⟩ = some ⟨4,([false,false,true,false]) ++ (L),([true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (5*n) ⟨4,([false,false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false,true]),([false,false,false,false])⟩ = some ⟨4,([false,false,true,false,false,true]),(rep [true,false,true] (n)) ++ ([false,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,false,true,false] [] [false,true,false] [true,false,true] 5 local1 n (([false,true])) (([false,false,false,false]))

theorem phase2 (n : Nat) : run0 table 10 ⟨4,([false,false,true,false,false,true]),(rep [true,false,true] (n)) ++ ([false,false,false,false])⟩ = some ⟨4,[],([true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([false,false,false,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([false,false,false,false]) = (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,false,false,false,false]) := by
  calc
    _ = ([true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true,false,false,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,true,false])) (([false,false,false,false])) [true,false] true n
    _ = ([true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,false,false,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,true])) (([true,false,false,false,false])) [true,true] false n
    _ = ([true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,false,false,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true])) (([false,true,false,false,false,false])) [false,true] true n
    _ = ([true,false]) ++ (rep [true,true,false] (n)) ++ ([true,true,false,true,false,false,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false])) (([true,false,true,false,false,false,false])) [true,false] true n
    _ = ([true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,false,true,false,false,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true])) (([true,true,false,true,false,false,false,false])) [true,true] false n
    _ = (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,false,false,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,true,true,false,true,false,false,false,false])) [false,true] true n

theorem epoch (n : Nat) : run0 table (25+5*n) ⟨2,([false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false,true]),([true,false,false,false,false])⟩ = some ⟨4,[],(rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,false,false,false,false])⟩ := by
  have H := (join0 (join0 (phase0 n) (phase1 n)) (phase2 n))
  rw [finalR n] at H
  rw [show 15+5*n+10=25+5*n by omega] at H
  exact H

theorem eq0l (n : Nat) : ([false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false,true]) = (rep [false,true,false] (n)) ++ ([false,true,false,false,true]) := by
  calc
    _ = ([false,true]) ++ (rep [false,false,true] (n)) ++ ([false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([false,true])) [false,true] false n
    _ = ([false]) ++ (rep [true,false,false] (n)) ++ ([true,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,true])) [false,false] true n
    _ = (rep [false,true,false] (n)) ++ ([false,true,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,false,false,true])) [true,false] false n

theorem eq1r (n : Nat) : (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,false,false,false,false]) = ([true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,false,false,false,false]) := by
  calc
    _ = ([true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,false,true,false,false,false,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,true,true,false,true,false,false,false,false])) [false,true] true n
    _ = ([true,false]) ++ (rep [true,true,false] (n)) ++ ([true,true,false,true,false,false,false,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true])) (([true,true,false,true,false,false,false,false])) [true,true] false n
    _ = ([true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,false,false,false,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false])) (([true,false,true,false,false,false,false])) [true,false] true n

theorem canon (n : Nat) : run0 table (25+5*n) ⟨2,(rep [false,true,false] (n)) ++ ([false,true,false,false,true]),([true,false,false,false,false])⟩ = some ⟨4,[],([true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,false,false,false,false])⟩ := by
  simpa only [eq0l n, eq1r n] using epoch n

end MFinish


namespace MCarry

-- 1RB0RC_1RC1LE_0RD0LF_1LD0RA_1LA0LB_0LE---

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | _,_ => none

theorem phase0 (n : Nat) (R : List Bool) : run0 table 15 ⟨2,([false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false,false,false]) ++ (R),([true,false,false,false,false])⟩ = some ⟨4,([false,false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false,false,false]) ++ (R),([false,false,false,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 5 ⟨4,([false,false,true,false]) ++ ([false,true,false]) ++ (L),(R)⟩ = some ⟨4,([false,false,true,false]) ++ (L),([true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) (R : List Bool) : run0 table (5*n) ⟨4,([false,false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false,false,false]) ++ (R),([false,false,false,false])⟩ = some ⟨4,([false,false,true,false,false,false,false]) ++ (R),(rep [true,false,true] (n)) ++ ([false,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,false,true,false] [] [false,true,false] [true,false,true] 5 local1 n (([false,false,false]) ++ (R)) (([false,false,false,false]))

theorem phase2 (n : Nat) (R : List Bool) : run0 table 10 ⟨4,([false,false,true,false,false,false,false]) ++ (R),(rep [true,false,true] (n)) ++ ([false,false,false,false])⟩ = some ⟨2,([false,true,false]) ++ (R),([true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([false,false,false,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨2,([false]) ++ (L),([true,true,false,true]) ++ ([true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([false,false,false]) ++ (L),([true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) (R : List Bool) : run0 table (3*n) ⟨2,([false,true,false]) ++ (R),([true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([false,false,false,false])⟩ = some ⟨2,([false]) ++ (rep [false,false,false] (n)) ++ ([true,false]) ++ (R),([true,true,false,true,false,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true] [true,false,true] [false,false,false] 3 local3 n (([true,false]) ++ (R)) (([false,false,false,false]))

theorem phase4 (n : Nat) (R : List Bool) : run0 table 3 ⟨2,([false]) ++ (rep [false,false,false] (n)) ++ ([true,false]) ++ (R),([true,true,false,true,false,false,false,false])⟩ = some ⟨2,([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,false]) ++ (R),([true,false,false,false,false])⟩ := by rfl

theorem finalL (n : Nat) (R : List Bool) : ([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,false]) ++ (R) = (rep [false,false,false] (n)) ++ ([false,false,false,false,true,false]) ++ (R) := by
  calc
    _ = ([false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,true,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false])) (([true,false]) ++ (R)) [false,false] false n
    _ = ([false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,true,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,true,false]) ++ (R)) [false,false] false n
    _ = ([false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,true,false]) ++ (R)) [false,false] false n
    _ = (rep [false,false,false] (n)) ++ ([false,false,false,false,true,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,false,false,true,false]) ++ (R)) [false,false] false n

theorem finalR (n : Nat) (R : List Bool) : ([true,false,false,false,false]) = ([true,false,false,false,false]) := by
  rfl

theorem epoch (n : Nat) (R : List Bool) : run0 table (28+8*n) ⟨2,([false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false,false,false]) ++ (R),([true,false,false,false,false])⟩ = some ⟨2,(rep [false,false,false] (n)) ++ ([false,false,false,false,true,false]) ++ (R),([true,false,false,false,false])⟩ := by
  have H := (join0 (join0 (join0 (join0 (phase0 n R) (phase1 n R)) (phase2 n R)) (phase3 n R)) (phase4 n R))
  rw [finalL n R] at H
  rw [show 15+5*n+10+3*n+3=28+8*n by omega] at H
  exact H

theorem eq0l (n : Nat) (R : List Bool) : ([false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false,false,false]) ++ (R) = (rep [false,true,false] (n)) ++ ([false,true,false,false,false,false]) ++ (R) := by
  calc
    _ = ([false,true]) ++ (rep [false,false,true] (n)) ++ ([false,false,false,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([false,false,false]) ++ (R)) [false,true] false n
    _ = ([false]) ++ (rep [true,false,false] (n)) ++ ([true,false,false,false,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,false,false]) ++ (R)) [false,false] true n
    _ = (rep [false,true,false] (n)) ++ ([false,true,false,false,false,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,false,false,false,false]) ++ (R)) [true,false] false n

theorem canon (n : Nat) (R : List Bool) : run0 table (28+8*n) ⟨2,(rep [false,true,false] (n)) ++ ([false,true,false,false,false,false]) ++ (R),([true,false,false,false,false])⟩ = some ⟨2,(rep [false,false,false] (n)) ++ ([false,false,false,false,true,false]) ++ (R),([true,false,false,false,false])⟩ := by
  simpa only [eq0l n R] using epoch n R

end MCarry


abbrev table := MInit.table
abbrev A : List Bool := [false,true,false]
abbrev Z : List Bool := [false,false,false]
def Q (R : List Bool) : Z0 := ⟨2,(R),[true,false,false,false,false]⟩
def family (n : Nat) : Z0 := ⟨4,[],(rep [true,false,true] (n)) ++ ([true,false,true,false,false,false,false])⟩
def carryCost (n : Nat) : Nat := 20+8*n

theorem carry (n : Nat) (R : List Bool) : run0 table (carryCost n) (Q (rep A n ++ Z ++ R)) = some (Q (rep Z n ++ A ++ R)) := by
  cases n with
  | zero => rfl
  | succ n =>
    have h := MCarry.canon n R
    rw [show MCarry.table = table from rfl] at h
    unfold carryCost
    rw [show 20+8*n.succ = 28+8*n by omega]
    rw [rep_succ_snoc A n,rep_succ_snoc Z n]
    simpa only [table,Q,A,Z,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem entry : run0 table 38 ⟨0,[],[]⟩ = some (family 0) := by rfl


def cost (n : Nat) : Nat := (8+3*n) + fillCost carryCost (n+1) + (25+5*n)

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := MInit.canon n
  have h2 := fill table Q A Z carryCost carry (n+1) [false,true]
  have h3 := MFinish.canon n
  rw [rep_add Z n 1,rep_add A n 1] at h2
  simp only [Q,A,Z,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] at h2
  have h := join0 (join0 h1 h2) h3
  simpa only [cost,family,rep,rep_succ_snoc,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 38 cost entry (by intro n; unfold cost; omega) growth m hm

#print axioms growth
#print axioms never
end M107
namespace M1

namespace MInit

-- 1RB0RC_1RC1LF_0RD0LE_1LD0RA_0LF---_1LA0LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 5 ⟨5,[],(rep [true,false,true] (n)) ++ ([true,false,true,false,false,false,false])⟩ = some ⟨2,([false,true]),([true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,false,false,false,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨2,([false]) ++ (L),([true]) ++ ([true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([false,false,false]) ++ (L),([true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨2,([false,true]),([true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,false,false,false,false])⟩ = some ⟨2,([false]) ++ (rep [false,false,false] (n)) ++ ([true]),([true,true,false,true,false,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true] [true,false,true] [false,false,false] 3 local1 n (([true])) (([true,false,true,false,false,false,false]))

theorem phase2 (n : Nat) : run0 table 3 ⟨2,([false]) ++ (rep [false,false,false] (n)) ++ ([true]),([true,true,false,true,false,false,false,false])⟩ = some ⟨2,([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]),([true,false,false,false,false])⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]) = (rep [false,false,false] (n)) ++ ([false,false,false,false,true]) := by
  calc
    _ = ([false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false])) (([true])) [false,false] false n
    _ = ([false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,true])) [false,false] false n
    _ = ([false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,true])) [false,false] false n
    _ = (rep [false,false,false] (n)) ++ ([false,false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,false,false,true])) [false,false] false n

theorem finalR (n : Nat) : ([true,false,false,false,false]) = ([true,false,false,false,false]) := by
  rfl

theorem epoch (n : Nat) : run0 table (8+3*n) ⟨5,[],(rep [true,false,true] (n)) ++ ([true,false,true,false,false,false,false])⟩ = some ⟨2,(rep [false,false,false] (n)) ++ ([false,false,false,false,true]),([true,false,false,false,false])⟩ := by
  have H := (join0 (join0 (phase0 n) (phase1 n)) (phase2 n))
  rw [finalL n] at H
  rw [show 5+3*n+3=8+3*n by omega] at H
  exact H

theorem canon (n : Nat) : run0 table (8+3*n) ⟨5,[],(rep [true,false,true] (n)) ++ ([true,false,true,false,false,false,false])⟩ = some ⟨2,(rep [false,false,false] (n)) ++ ([false,false,false,false,true]),([true,false,false,false,false])⟩ := by
  exact epoch n

end MInit


namespace MFinish

-- 1RB0RC_1RC1LF_0RD0LE_1LD0RA_0LF---_1LA0LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 15 ⟨2,([false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false,true]),([true,false,false,false,false])⟩ = some ⟨5,([false,false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false,true]),([false,false,false,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 5 ⟨5,([false,false,true,false]) ++ ([false,true,false]) ++ (L),(R)⟩ = some ⟨5,([false,false,true,false]) ++ (L),([true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (5*n) ⟨5,([false,false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false,true]),([false,false,false,false])⟩ = some ⟨5,([false,false,true,false,false,true]),(rep [true,false,true] (n)) ++ ([false,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,true,false] [] [false,true,false] [true,false,true] 5 local1 n (([false,true])) (([false,false,false,false]))

theorem phase2 (n : Nat) : run0 table 10 ⟨5,([false,false,true,false,false,true]),(rep [true,false,true] (n)) ++ ([false,false,false,false])⟩ = some ⟨5,[],([true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([false,false,false,false])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([false,false,false,false]) = (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,false,false,false,false]) := by
  calc
    _ = ([true,false,true,true,false]) ++ (rep [true,true,false] (n)) ++ ([true,false,false,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,true,false])) (([false,false,false,false])) [true,false] true n
    _ = ([true,false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,false,false,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true,true])) (([true,false,false,false,false])) [true,true] false n
    _ = ([true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,false,false,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,true])) (([false,true,false,false,false,false])) [false,true] true n
    _ = ([true,false]) ++ (rep [true,true,false] (n)) ++ ([true,true,false,true,false,false,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false])) (([true,false,true,false,false,false,false])) [true,false] true n
    _ = ([true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,false,true,false,false,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true])) (([true,true,false,true,false,false,false,false])) [true,true] false n
    _ = (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,false,false,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,true,true,false,true,false,false,false,false])) [false,true] true n

theorem epoch (n : Nat) : run0 table (25+5*n) ⟨2,([false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false,true]),([true,false,false,false,false])⟩ = some ⟨5,[],(rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,false,false,false,false])⟩ := by
  have H := (join0 (join0 (phase0 n) (phase1 n)) (phase2 n))
  rw [finalR n] at H
  rw [show 15+5*n+10=25+5*n by omega] at H
  exact H

theorem eq0l (n : Nat) : ([false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false,true]) = (rep [false,true,false] (n)) ++ ([false,true,false,false,true]) := by
  calc
    _ = ([false,true]) ++ (rep [false,false,true] (n)) ++ ([false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([false,true])) [false,true] false n
    _ = ([false]) ++ (rep [true,false,false] (n)) ++ ([true,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,true])) [false,false] true n
    _ = (rep [false,true,false] (n)) ++ ([false,true,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,false,false,true])) [true,false] false n

theorem eq1r (n : Nat) : (rep [true,false,true] (n)) ++ ([true,false,true,true,false,true,false,false,false,false]) = ([true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,false,false,false,false]) := by
  calc
    _ = ([true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,false,true,false,false,false,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,true,true,false,true,false,false,false,false])) [false,true] true n
    _ = ([true,false]) ++ (rep [true,true,false] (n)) ++ ([true,true,false,true,false,false,false,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true])) (([true,true,false,true,false,false,false,false])) [true,true] false n
    _ = ([true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,false,false,false,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false])) (([true,false,true,false,false,false,false])) [true,false] true n

theorem canon (n : Nat) : run0 table (25+5*n) ⟨2,(rep [false,true,false] (n)) ++ ([false,true,false,false,true]),([true,false,false,false,false])⟩ = some ⟨5,[],([true,false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,false,false,false,false])⟩ := by
  simpa only [eq0l n, eq1r n] using epoch n

end MFinish


namespace MCarry

-- 1RB0RC_1RC1LF_0RD0LE_1LD0RA_0LF---_1LA0LB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

theorem phase0 (n : Nat) (R : List Bool) : run0 table 15 ⟨2,([false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false,false,false]) ++ (R),([true,false,false,false,false])⟩ = some ⟨5,([false,false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false,false,false]) ++ (R),([false,false,false,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 5 ⟨5,([false,false,true,false]) ++ ([false,true,false]) ++ (L),(R)⟩ = some ⟨5,([false,false,true,false]) ++ (L),([true,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) (R : List Bool) : run0 table (5*n) ⟨5,([false,false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false,false,false]) ++ (R),([false,false,false,false])⟩ = some ⟨5,([false,false,true,false,false,false,false]) ++ (R),(rep [true,false,true] (n)) ++ ([false,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,true,false] [] [false,true,false] [true,false,true] 5 local1 n (([false,false,false]) ++ (R)) (([false,false,false,false]))

theorem phase2 (n : Nat) (R : List Bool) : run0 table 10 ⟨5,([false,false,true,false,false,false,false]) ++ (R),(rep [true,false,true] (n)) ++ ([false,false,false,false])⟩ = some ⟨2,([false,true,false]) ++ (R),([true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([false,false,false,false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨2,([false]) ++ (L),([true,true,false,true]) ++ ([true,false,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([false,false,false]) ++ (L),([true,true,false,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) (R : List Bool) : run0 table (3*n) ⟨2,([false,true,false]) ++ (R),([true,true,false,true]) ++ (rep [true,false,true] (n)) ++ ([false,false,false,false])⟩ = some ⟨2,([false]) ++ (rep [false,false,false] (n)) ++ ([true,false]) ++ (R),([true,true,false,true,false,false,false,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true,false,true] [true,false,true] [false,false,false] 3 local3 n (([true,false]) ++ (R)) (([false,false,false,false]))

theorem phase4 (n : Nat) (R : List Bool) : run0 table 3 ⟨2,([false]) ++ (rep [false,false,false] (n)) ++ ([true,false]) ++ (R),([true,true,false,true,false,false,false,false])⟩ = some ⟨2,([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,false]) ++ (R),([true,false,false,false,false])⟩ := by rfl

theorem finalL (n : Nat) (R : List Bool) : ([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,false]) ++ (R) = (rep [false,false,false] (n)) ++ ([false,false,false,false,true,false]) ++ (R) := by
  calc
    _ = ([false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,true,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false])) (([true,false]) ++ (R)) [false,false] false n
    _ = ([false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,true,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,true,false]) ++ (R)) [false,false] false n
    _ = ([false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,true,false]) ++ (R)) [false,false] false n
    _ = (rep [false,false,false] (n)) ++ ([false,false,false,false,true,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,false,false,true,false]) ++ (R)) [false,false] false n

theorem finalR (n : Nat) (R : List Bool) : ([true,false,false,false,false]) = ([true,false,false,false,false]) := by
  rfl

theorem epoch (n : Nat) (R : List Bool) : run0 table (28+8*n) ⟨2,([false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false,false,false]) ++ (R),([true,false,false,false,false])⟩ = some ⟨2,(rep [false,false,false] (n)) ++ ([false,false,false,false,true,false]) ++ (R),([true,false,false,false,false])⟩ := by
  have H := (join0 (join0 (join0 (join0 (phase0 n R) (phase1 n R)) (phase2 n R)) (phase3 n R)) (phase4 n R))
  rw [finalL n R] at H
  rw [show 15+5*n+10+3*n+3=28+8*n by omega] at H
  exact H

theorem eq0l (n : Nat) (R : List Bool) : ([false,true,false]) ++ (rep [false,true,false] (n)) ++ ([false,false,false]) ++ (R) = (rep [false,true,false] (n)) ++ ([false,true,false,false,false,false]) ++ (R) := by
  calc
    _ = ([false,true]) ++ (rep [false,false,true] (n)) ++ ([false,false,false,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([false,false,false]) ++ (R)) [false,true] false n
    _ = ([false]) ++ (rep [true,false,false] (n)) ++ ([true,false,false,false,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,false,false]) ++ (R)) [false,false] true n
    _ = (rep [false,true,false] (n)) ++ ([false,true,false,false,false,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,false,false,false,false]) ++ (R)) [true,false] false n

theorem canon (n : Nat) (R : List Bool) : run0 table (28+8*n) ⟨2,(rep [false,true,false] (n)) ++ ([false,true,false,false,false,false]) ++ (R),([true,false,false,false,false])⟩ = some ⟨2,(rep [false,false,false] (n)) ++ ([false,false,false,false,true,false]) ++ (R),([true,false,false,false,false])⟩ := by
  simpa only [eq0l n R] using epoch n R

end MCarry


abbrev table := MInit.table
abbrev A : List Bool := [false,true,false]
abbrev Z : List Bool := [false,false,false]
def Q (R : List Bool) : Z0 := ⟨2,(R),[true,false,false,false,false]⟩
def family (n : Nat) : Z0 := ⟨5,[],(rep [true,false,true] (n)) ++ ([true,false,true,false,false,false,false])⟩
def carryCost (n : Nat) : Nat := 20+8*n

theorem carry (n : Nat) (R : List Bool) : run0 table (carryCost n) (Q (rep A n ++ Z ++ R)) = some (Q (rep Z n ++ A ++ R)) := by
  cases n with
  | zero => rfl
  | succ n =>
    have h := MCarry.canon n R
    rw [show MCarry.table = table from rfl] at h
    unfold carryCost
    rw [show 20+8*n.succ = 28+8*n by omega]
    rw [rep_succ_snoc A n,rep_succ_snoc Z n]
    simpa only [table,Q,A,Z,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem entry : run0 table 38 ⟨0,[],[]⟩ = some (family 0) := by rfl


def cost (n : Nat) : Nat := (8+3*n) + fillCost carryCost (n+1) + (25+5*n)

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := MInit.canon n
  have h2 := fill table Q A Z carryCost carry (n+1) [false,true]
  have h3 := MFinish.canon n
  rw [rep_add Z n 1,rep_add A n 1] at h2
  simp only [Q,A,Z,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] at h2
  have h := join0 (join0 h1 h2) h3
  simpa only [cost,family,rep,rep_succ_snoc,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 38 cost entry (by intro n; unfold cost; omega) growth m hm

#print axioms growth
#print axioms never
end M1

end BB6.Agent11Raw39RCCounter107
