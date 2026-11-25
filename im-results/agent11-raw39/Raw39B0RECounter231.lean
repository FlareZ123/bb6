import Raw39CounterCarry
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent11CounterCarry
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B0RECounter231
namespace M231

namespace MInit

-- 1RB0RE_1RC0RA_0RD---_1LD0RA_0RB0LF_1LF1RA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 6 ⟨2,([false,true,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]),[]⟩ = some ⟨5,([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]),([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨5,([false,false,false,false]) ++ ([false,false,false]) ++ (L),(R)⟩ = some ⟨5,([false,false,false,false]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨5,([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]),([false])⟩ = some ⟨5,([false,false,false,false,true]),(rep [true,true,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,false,false] [] [false,false,false] [true,true,true] 3 local1 n (([true])) (([false]))

theorem finalL (n : Nat) : ([false,false,false,false,true]) = ([false,false,false,false,true]) := by
  rfl

theorem finalR (n : Nat) : (rep [true,true,true] (n)) ++ ([false]) = (rep [true,true,true] (n)) ++ ([false]) := by
  rfl

theorem epoch (n : Nat) : run0 table (6+3*n) ⟨2,([false,true,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]),[]⟩ = some ⟨5,([false,false,false,false,true]),(rep [true,true,true] (n)) ++ ([false])⟩ := by
  have H := (join0 (phase0 n) (phase1 n))
  rw [show 6+3*n=6+3*n by omega] at H
  exact H

theorem canon (n : Nat) : run0 table (6+3*n) ⟨2,([false,true,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]),[]⟩ = some ⟨5,([false,false,false,false,true]),(rep [true,true,true] (n)) ++ ([false])⟩ := by
  exact epoch n

end MInit


namespace MFinish

-- 1RB0RE_1RC0RA_0RD---_1LD0RA_0RB0LF_1LF1RA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 9 ⟨5,([false,false,false,false,true]),(rep [false,true,true] (n)) ++ ([false])⟩ = some ⟨0,([true,true]),([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨0,([true]) ++ (L),([false,true,true]) ++ ([false,true,true]) ++ (R)⟩ = some ⟨0,([true]) ++ ([false,false,false]) ++ (L),([false,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨0,([true,true]),([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false])⟩ = some ⟨0,([true]) ++ (rep [false,false,false] (n)) ++ ([true]),([false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [true] [false,true,true] [false,true,true] [false,false,false] 3 local1 n (([true])) (([false]))

theorem phase2 (n : Nat) : run0 table 6 ⟨0,([true]) ++ (rep [false,false,false] (n)) ++ ([true]),([false,true,true,false])⟩ = some ⟨2,([false,true,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]) = ([false,true,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true]) := by
  calc
    _ = ([false,true,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,false,false])) (([true])) [false,false] false n
    _ = ([false,true,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,false])) (([false,true])) [false,false] false n
    _ = ([false,true,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false])) (([false,false,true])) [false,false] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem epoch (n : Nat) : run0 table (15+3*n) ⟨5,([false,false,false,false,true]),(rep [false,true,true] (n)) ++ ([false])⟩ = some ⟨2,([false,true,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true]),[]⟩ := by
  have H := (join0 (join0 (phase0 n) (phase1 n)) (phase2 n))
  rw [finalL n] at H
  rw [show 9+3*n+6=15+3*n by omega] at H
  exact H

theorem eq1l (n : Nat) : ([false,true,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true]) = ([false,true,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]) := by
  calc
    _ = ([false,true,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false])) (([false,false,true])) [false,false] false n
    _ = ([false,true,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,false])) (([false,true])) [false,false] false n
    _ = ([false,true,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,false,false])) (([true])) [false,false] false n

theorem canon (n : Nat) : run0 table (15+3*n) ⟨5,([false,false,false,false,true]),(rep [false,true,true] (n)) ++ ([false])⟩ = some ⟨2,([false,true,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]),[]⟩ := by
  simpa only [eq1l n] using epoch n

end MFinish


namespace MCarry

-- 1RB0RE_1RC0RA_0RD---_1LD0RA_0RB0LF_1LF1RA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none

theorem phase0 (n : Nat) (R : List Bool) : run0 table 9 ⟨5,([false,false,false,false,true]),(rep [false,true,true] (n)) ++ ([false,true,true,true,true,true]) ++ (R)⟩ = some ⟨0,([true,true]),([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,true,true,true]) ++ (R)⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨0,([true]) ++ (L),([false,true,true]) ++ ([false,true,true]) ++ (R)⟩ = some ⟨0,([true]) ++ ([false,false,false]) ++ (L),([false,true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) (R : List Bool) : run0 table (3*n) ⟨0,([true,true]),([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,true,true,true]) ++ (R)⟩ = some ⟨0,([true]) ++ (rep [false,false,false] (n)) ++ ([true]),([false,true,true,false,true,true,true,true,true]) ++ (R)⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [true] [false,true,true] [false,true,true] [false,false,false] 3 local1 n (([true])) (([false,true,true,true,true,true]) ++ (R))

theorem phase2 (n : Nat) (R : List Bool) : run0 table 8 ⟨0,([true]) ++ (rep [false,false,false] (n)) ++ ([true]),([false,true,true,false,true,true,true,true,true]) ++ (R)⟩ = some ⟨5,([false,false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]),([false,true,true]) ++ (R)⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨5,([false,false,false,false,false,false,false]) ++ ([false,false,false]) ++ (L),(R)⟩ = some ⟨5,([false,false,false,false,false,false,false]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) (R : List Bool) : run0 table (3*n) ⟨5,([false,false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]),([false,true,true]) ++ (R)⟩ = some ⟨5,([false,false,false,false,false,false,false,true]),(rep [true,true,true] (n)) ++ ([false,true,true]) ++ (R)⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,false,false,false,false,false] [] [false,false,false] [true,true,true] 3 local3 n (([true])) (([false,true,true]) ++ (R))

theorem phase4 (n : Nat) (R : List Bool) : run0 table 3 ⟨5,([false,false,false,false,false,false,false,true]),(rep [true,true,true] (n)) ++ ([false,true,true]) ++ (R)⟩ = some ⟨5,([false,false,false,false,true]),([true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false,true,true]) ++ (R)⟩ := by rfl

theorem finalL (n : Nat) (R : List Bool) : ([false,false,false,false,true]) = ([false,false,false,false,true]) := by
  rfl

theorem finalR (n : Nat) (R : List Bool) : ([true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false,true,true]) ++ (R) = (rep [true,true,true] (n)) ++ ([true,true,true,false,true,true]) ++ (R) := by
  calc
    _ = ([true,true]) ++ (rep [true,true,true] (n)) ++ ([true,false,true,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true])) (([false,true,true]) ++ (R)) [true,true] true n
    _ = ([true]) ++ (rep [true,true,true] (n)) ++ ([true,true,false,true,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true])) (([true,false,true,true]) ++ (R)) [true,true] true n
    _ = (rep [true,true,true] (n)) ++ ([true,true,true,false,true,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,true,false,true,true]) ++ (R)) [true,true] true n

theorem epoch (n : Nat) (R : List Bool) : run0 table (20+6*n) ⟨5,([false,false,false,false,true]),(rep [false,true,true] (n)) ++ ([false,true,true,true,true,true]) ++ (R)⟩ = some ⟨5,([false,false,false,false,true]),(rep [true,true,true] (n)) ++ ([true,true,true,false,true,true]) ++ (R)⟩ := by
  have H := (join0 (join0 (join0 (join0 (phase0 n R) (phase1 n R)) (phase2 n R)) (phase3 n R)) (phase4 n R))
  rw [finalR n R] at H
  rw [show 9+3*n+8+3*n+3=20+6*n by omega] at H
  exact H

theorem canon (n : Nat) (R : List Bool) : run0 table (20+6*n) ⟨5,([false,false,false,false,true]),(rep [false,true,true] (n)) ++ ([false,true,true,true,true,true]) ++ (R)⟩ = some ⟨5,([false,false,false,false,true]),(rep [true,true,true] (n)) ++ ([true,true,true,false,true,true]) ++ (R)⟩ := by
  exact epoch n R

end MCarry


abbrev table := MInit.table
abbrev A : List Bool := [false,true,true]
abbrev Z : List Bool := [true,true,true]
def Q (R : List Bool) : Z0 := ⟨5,[false,false,false,false,true],(R)⟩
def family (n : Nat) : Z0 := ⟨2,([false,true,false,false]) ++ (rep [false,false,false] (n)) ++ ([true]),[]⟩
def carryCost (n : Nat) : Nat := 14+6*n

theorem carry (n : Nat) (R : List Bool) : run0 table (carryCost n) (Q (rep A n ++ Z ++ R)) = some (Q (rep Z n ++ A ++ R)) := by
  cases n with
  | zero => rfl
  | succ n =>
    have h := MCarry.canon n R
    rw [show MCarry.table = table from rfl] at h
    unfold carryCost
    rw [show 14+6*n.succ = 20+6*n by omega]
    rw [rep_succ_snoc A n,rep_succ_snoc Z n]
    simpa only [table,Q,A,Z,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem entry : run0 table 18 ⟨0,[],[]⟩ = some (family 0) := by rfl


def cost (n : Nat) : Nat := (6+3*n) + fillCost carryCost (n+0) + (15+3*n)
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := MInit.canon n
  have h2 := fill table Q A Z carryCost carry (n+0) [false]
  have h3 := MFinish.canon n
  rw [rep_add Z n 0,rep_add A n 0] at h2
  simp only [Q,A,Z,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] at h2
  have h := join0 (join0 h1 h2) h3
  simpa only [cost,family,rep,rep_succ_snoc,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 18 cost entry (by intro n; unfold cost; omega) growth m hm

#print axioms growth
#print axioms never
end M231

end BB6.Agent11Raw39B0RECounter231
