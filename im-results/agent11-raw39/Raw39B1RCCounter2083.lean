import Raw39CounterCarry
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent11CounterCarry
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B1RCCounter2083
namespace M2083

namespace MInit

-- 1RB1RC_1RC0LB_0RD1RF_1LD0RA_0RF---_1LB1RE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,true,4⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 1 ⟨5,([false,true,true]) ++ (rep [true,true,true] (n)) ++ ([false,true]),[]⟩ = some ⟨1,([true,true]) ++ (rep [true,true,true] (n)) ++ ([false,true]),([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨1,([true,true]) ++ ([true,true,true]) ++ (L),(R)⟩ = some ⟨1,([true,true]) ++ (L),([false,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨1,([true,true]) ++ (rep [true,true,true] (n)) ++ ([false,true]),([true])⟩ = some ⟨1,([true,true,false,true]),(rep [false,false,false] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true] [] [true,true,true] [false,false,false] 3 local1 n (([false,true])) (([true]))

theorem phase2 (n : Nat) : run0 table 3 ⟨1,([true,true,false,true]),(rep [false,false,false] (n)) ++ ([true])⟩ = some ⟨2,([false,true,true]),([false]) ++ (rep [false,false,false] (n)) ++ ([true])⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true]) = ([false,true,true]) := by
  rfl

theorem finalR (n : Nat) : ([false]) ++ (rep [false,false,false] (n)) ++ ([true]) = ([false]) ++ (rep [false,false,false] (n)) ++ ([true]) := by
  rfl

theorem epoch (n : Nat) : run0 table (4+3*n) ⟨5,([false,true,true]) ++ (rep [true,true,true] (n)) ++ ([false,true]),[]⟩ = some ⟨2,([false,true,true]),([false]) ++ (rep [false,false,false] (n)) ++ ([true])⟩ := by
  have H := (join0 (join0 (phase0 n) (phase1 n)) (phase2 n))
  rw [show 1+3*n+3=4+3*n by omega] at H
  exact H

theorem canon (n : Nat) : run0 table (4+3*n) ⟨5,([false,true,true]) ++ (rep [true,true,true] (n)) ++ ([false,true]),[]⟩ = some ⟨2,([false,true,true]),([false]) ++ (rep [false,false,false] (n)) ++ ([true])⟩ := by
  exact epoch n

end MInit


namespace MFinish

-- 1RB1RC_1RC0LB_0RD1RF_1LD0RA_0RF---_1LB1RE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,true,4⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 5 ⟨2,([false,true,true]),([false]) ++ (rep [true,false,false] (n)) ++ ([true])⟩ = some ⟨2,([true,true,false,true]),(rep [true,false,false] (n)) ++ ([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 5 ⟨2,([true]) ++ (L),([true,false,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true,true]) ++ (L),(R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (5*n) ⟨2,([true,true,false,true]),(rep [true,false,false] (n)) ++ ([true])⟩ = some ⟨2,([true]) ++ (rep [true,true,true] (n)) ++ ([true,false,true]),([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [] [true,false,false] [true,true,true] 5 local1 n (([true,false,true])) (([true]))

theorem phase2 (n : Nat) : run0 table 6 ⟨2,([true]) ++ (rep [true,true,true] (n)) ++ ([true,false,true]),([true])⟩ = some ⟨5,([false,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,false,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,false,true]) = ([false,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,false,true]) := by
  calc
    _ = ([false,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true])) (([true,false,true])) [true,true] true n
    _ = ([false,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true])) (([true,true,false,true])) [true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem epoch (n : Nat) : run0 table (11+5*n) ⟨2,([false,true,true]),([false]) ++ (rep [true,false,false] (n)) ++ ([true])⟩ = some ⟨5,([false,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,false,true]),[]⟩ := by
  have H := (join0 (join0 (phase0 n) (phase1 n)) (phase2 n))
  rw [finalL n] at H
  rw [show 5+5*n+6=11+5*n by omega] at H
  exact H

theorem eq1l (n : Nat) : ([false,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,false,true]) = ([false,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false,true]) := by
  calc
    _ = ([false,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true])) (([true,true,false,true])) [true,true] true n
    _ = ([false,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true])) (([true,false,true])) [true,true] true n
    _ = ([false,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,true,true])) (([false,true])) [true,true] true n

theorem canon (n : Nat) : run0 table (11+5*n) ⟨2,([false,true,true]),([false]) ++ (rep [true,false,false] (n)) ++ ([true])⟩ = some ⟨5,([false,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false,true]),[]⟩ := by
  simpa only [eq1l n] using epoch n

end MFinish


namespace MCarry

-- 1RB1RC_1RC0LB_0RD1RF_1LD0RA_0RF---_1LB1RE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,true,4⟩)
  | _,_ => none

theorem phase0 (n : Nat) (R : List Bool) : run0 table 5 ⟨2,([false,true,true]),([false]) ++ (rep [true,false,false] (n)) ++ ([true,false,false,false,false,false]) ++ (R)⟩ = some ⟨2,([true,true,false,true]),(rep [true,false,false] (n)) ++ ([true,false,false,false,false,false]) ++ (R)⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 5 ⟨2,([true]) ++ (L),([true,false,false]) ++ (R)⟩ = some ⟨2,([true]) ++ ([true,true,true]) ++ (L),(R)⟩ := by rfl

theorem phase1 (n : Nat) (R : List Bool) : run0 table (5*n) ⟨2,([true,true,false,true]),(rep [true,false,false] (n)) ++ ([true,false,false,false,false,false]) ++ (R)⟩ = some ⟨2,([true]) ++ (rep [true,true,true] (n)) ++ ([true,false,true]),([true,false,false,false,false,false]) ++ (R)⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [true] [] [true,false,false] [true,true,true] 5 local1 n (([true,false,true])) (([true,false,false,false,false,false]) ++ (R))

theorem phase2 (n : Nat) (R : List Bool) : run0 table 7 ⟨2,([true]) ++ (rep [true,true,true] (n)) ++ ([true,false,true]),([true,false,false,false,false,false]) ++ (R)⟩ = some ⟨1,([true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,false,true]),([true,false,false]) ++ (R)⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨1,([true,true,true,true]) ++ ([true,true,true]) ++ (L),(R)⟩ = some ⟨1,([true,true,true,true]) ++ (L),([false,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) (R : List Bool) : run0 table (3*n) ⟨1,([true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,false,true]),([true,false,false]) ++ (R)⟩ = some ⟨1,([true,true,true,true,true,false,true]),(rep [false,false,false] (n)) ++ ([true,false,false]) ++ (R)⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 1 [true,true,true,true] [] [true,true,true] [false,false,false] 3 local3 n (([true,false,true])) (([true,false,false]) ++ (R))

theorem phase4 (n : Nat) (R : List Bool) : run0 table 6 ⟨1,([true,true,true,true,true,false,true]),(rep [false,false,false] (n)) ++ ([true,false,false]) ++ (R)⟩ = some ⟨2,([false,true,true]),([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,false,false]) ++ (R)⟩ := by rfl

theorem finalL (n : Nat) (R : List Bool) : ([false,true,true]) = ([false,true,true]) := by
  rfl

theorem finalR (n : Nat) (R : List Bool) : ([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,false,false]) ++ (R) = ([false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true,false,false]) ++ (R) := by
  calc
    _ = ([false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,true,false,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false])) (([true,false,false]) ++ (R)) [false,false] false n
    _ = ([false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,true,false,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,true,false,false]) ++ (R)) [false,false] false n
    _ = ([false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true,false,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,true,false,false]) ++ (R)) [false,false] false n

theorem epoch (n : Nat) (R : List Bool) : run0 table (18+8*n) ⟨2,([false,true,true]),([false]) ++ (rep [true,false,false] (n)) ++ ([true,false,false,false,false,false]) ++ (R)⟩ = some ⟨2,([false,true,true]),([false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true,false,false]) ++ (R)⟩ := by
  have H := (join0 (join0 (join0 (join0 (phase0 n R) (phase1 n R)) (phase2 n R)) (phase3 n R)) (phase4 n R))
  rw [finalR n R] at H
  rw [show 5+5*n+7+3*n+6=18+8*n by omega] at H
  exact H

theorem canon (n : Nat) (R : List Bool) : run0 table (18+8*n) ⟨2,([false,true,true]),([false]) ++ (rep [true,false,false] (n)) ++ ([true,false,false,false,false,false]) ++ (R)⟩ = some ⟨2,([false,true,true]),([false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true,false,false]) ++ (R)⟩ := by
  exact epoch n R

end MCarry


abbrev table := MInit.table
abbrev A : List Bool := [true,false,false]
abbrev Z : List Bool := [false,false,false]
def Q (R : List Bool) : Z0 := ⟨2,[false,true,true],([false]) ++ (R)⟩
def family (n : Nat) : Z0 := ⟨5,([false,true,true]) ++ (rep [true,true,true] (n)) ++ ([false,true]),[]⟩
def carryCost (n : Nat) : Nat := 10+8*n

theorem carry (n : Nat) (R : List Bool) : run0 table (carryCost n) (Q (rep A n ++ Z ++ R)) = some (Q (rep Z n ++ A ++ R)) := by
  cases n with
  | zero => rfl
  | succ n =>
    have h := MCarry.canon n R
    rw [show MCarry.table = table from rfl] at h
    unfold carryCost
    rw [show 10+8*n.succ = 18+8*n by omega]
    rw [rep_succ_snoc A n,rep_succ_snoc Z n]
    simpa only [table,Q,A,Z,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl


def cost (n : Nat) : Nat := (4+3*n) + fillCost carryCost (n+0) + (11+5*n)
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := MInit.canon n
  have h2 := fill table Q A Z carryCost carry (n+0) [true]
  have h3 := MFinish.canon n
  rw [rep_add Z n 0,rep_add A n 0] at h2
  simp only [Q,A,Z,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] at h2
  have h := join0 (join0 h1 h2) h3
  simpa only [cost,family,rep,rep_succ_snoc,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 cost entry (by intro n; unfold cost; omega) growth m hm

#print axioms growth
#print axioms never
end M2083

end BB6.Agent11Raw39B1RCCounter2083
