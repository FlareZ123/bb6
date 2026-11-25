import Raw39CounterCarry
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent11CounterCarry
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B0RECounter2481
namespace M2481

namespace MInit

-- 1RB0RE_1RC1LD_0RD---_1LD0RA_1LF1RE_0LF1RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 6 ⟨4,([false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true]),[]⟩ = some ⟨5,([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]),([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨5,([false,false,false,false]) ++ ([false,false]) ++ (L),(R)⟩ = some ⟨5,([false,false,false,false]) ++ (L),([false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨5,([false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]),([true])⟩ = some ⟨5,([false,false,false,false,true]),(rep [false,false] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,false,false] [] [false,false] [false,false] 2 local1 n (([true])) (([true]))

theorem finalL (n : Nat) : ([false,false,false,false,true]) = ([false,false,false,false,true]) := by
  rfl

theorem finalR (n : Nat) : (rep [false,false] (n)) ++ ([true]) = (rep [false,false] (n)) ++ ([true]) := by
  rfl

theorem epoch (n : Nat) : run0 table (6+2*n) ⟨4,([false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true]),[]⟩ = some ⟨5,([false,false,false,false,true]),(rep [false,false] (n)) ++ ([true])⟩ := by
  have H := (join0 (phase0 n) (phase1 n))
  rw [show 6+2*n=6+2*n by omega] at H
  exact H

theorem canon (n : Nat) : run0 table (6+2*n) ⟨4,([false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true]),[]⟩ = some ⟨5,([false,false,false,false,true]),(rep [false,false] (n)) ++ ([true])⟩ := by
  exact epoch n

end MInit


namespace MFinish

-- 1RB0RE_1RC1LD_0RD---_1LD0RA_1LF1RE_0LF1RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 9 ⟨5,([false,false,false,false,true]),(rep [true,false] (n)) ++ ([true])⟩ = some ⟨3,([true,true]),([true,true,false]) ++ (rep [true,false] (n)) ++ ([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨3,([true]) ++ (L),([true,true,false]) ++ ([true,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,false]) ++ (L),([true,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨3,([true,true]),([true,true,false]) ++ (rep [true,false] (n)) ++ ([true])⟩ = some ⟨3,([true]) ++ (rep [false,false] (n)) ++ ([true]),([true,true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true,true,false] [true,false] [false,false] 6 local1 n (([true])) (([true]))

theorem phase2 (n : Nat) : run0 table 9 ⟨3,([true]) ++ (rep [false,false] (n)) ++ ([true]),([true,true,false,true])⟩ = some ⟨4,([false,true,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]) = ([false,true,false,false]) ++ (rep [false,false] (n)) ++ ([false,false,true]) := by
  calc
    _ = ([false,true,false,false,false]) ++ (rep [false,false] (n)) ++ ([false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,false])) (([true])) [false] false n
    _ = ([false,true,false,false]) ++ (rep [false,false] (n)) ++ ([false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false])) (([false,true])) [false] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem epoch (n : Nat) : run0 table (18+6*n) ⟨5,([false,false,false,false,true]),(rep [true,false] (n)) ++ ([true])⟩ = some ⟨4,([false,true,false,false]) ++ (rep [false,false] (n)) ++ ([false,false,true]),[]⟩ := by
  have H := (join0 (join0 (phase0 n) (phase1 n)) (phase2 n))
  rw [finalL n] at H
  rw [show 9+6*n+9=18+6*n by omega] at H
  exact H

theorem eq1l (n : Nat) : ([false,true,false,false]) ++ (rep [false,false] (n)) ++ ([false,false,true]) = ([false,true,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]) := by
  calc
    _ = ([false,true,false,false,false]) ++ (rep [false,false] (n)) ++ ([false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false])) (([false,true])) [false] false n
    _ = ([false,true,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,false,false,false])) (([true])) [false] false n

theorem canon (n : Nat) : run0 table (18+6*n) ⟨5,([false,false,false,false,true]),(rep [true,false] (n)) ++ ([true])⟩ = some ⟨4,([false,true,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]),[]⟩ := by
  simpa only [eq1l n] using epoch n

end MFinish


namespace MCarry

-- 1RB0RE_1RC1LD_0RD---_1LD0RA_1LF1RE_0LF1RB

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem phase0 (n : Nat) (R : List Bool) : run0 table 9 ⟨5,([false,false,false,false,true]),(rep [true,false] (n)) ++ ([true,false,false,false]) ++ (R)⟩ = some ⟨3,([true,true]),([true,true,false]) ++ (rep [true,false] (n)) ++ ([true,false,false,false]) ++ (R)⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨3,([true]) ++ (L),([true,true,false]) ++ ([true,false]) ++ (R)⟩ = some ⟨3,([true]) ++ ([false,false]) ++ (L),([true,true,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) (R : List Bool) : run0 table (6*n) ⟨3,([true,true]),([true,true,false]) ++ (rep [true,false] (n)) ++ ([true,false,false,false]) ++ (R)⟩ = some ⟨3,([true]) ++ (rep [false,false] (n)) ++ ([true]),([true,true,false,true,false,false,false]) ++ (R)⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 3 [true] [true,true,false] [true,false] [false,false] 6 local1 n (([true])) (([true,false,false,false]) ++ (R))

theorem phase2 (n : Nat) (R : List Bool) : run0 table 15 ⟨3,([true]) ++ (rep [false,false] (n)) ++ ([true]),([true,true,false,true,false,false,false]) ++ (R)⟩ = some ⟨5,([false,false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]),([true,false]) ++ (R)⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 2 ⟨5,([false,false,false,false,false,false]) ++ ([false,false]) ++ (L),(R)⟩ = some ⟨5,([false,false,false,false,false,false]) ++ (L),([false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) (R : List Bool) : run0 table (2*n) ⟨5,([false,false,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true]),([true,false]) ++ (R)⟩ = some ⟨5,([false,false,false,false,false,false,true]),(rep [false,false] (n)) ++ ([true,false]) ++ (R)⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,false,false,false,false] [] [false,false] [false,false] 2 local3 n (([true])) (([true,false]) ++ (R))

theorem phase4 (n : Nat) (R : List Bool) : run0 table 2 ⟨5,([false,false,false,false,false,false,true]),(rep [false,false] (n)) ++ ([true,false]) ++ (R)⟩ = some ⟨5,([false,false,false,false,true]),([false,false]) ++ (rep [false,false] (n)) ++ ([true,false]) ++ (R)⟩ := by rfl

theorem finalL (n : Nat) (R : List Bool) : ([false,false,false,false,true]) = ([false,false,false,false,true]) := by
  rfl

theorem finalR (n : Nat) (R : List Bool) : ([false,false]) ++ (rep [false,false] (n)) ++ ([true,false]) ++ (R) = (rep [false,false] (n)) ++ ([false,false,true,false]) ++ (R) := by
  calc
    _ = ([false]) ++ (rep [false,false] (n)) ++ ([false,true,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([true,false]) ++ (R)) [false] false n
    _ = (rep [false,false] (n)) ++ ([false,false,true,false]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,true,false]) ++ (R)) [false] false n

theorem epoch (n : Nat) (R : List Bool) : run0 table (26+8*n) ⟨5,([false,false,false,false,true]),(rep [true,false] (n)) ++ ([true,false,false,false]) ++ (R)⟩ = some ⟨5,([false,false,false,false,true]),(rep [false,false] (n)) ++ ([false,false,true,false]) ++ (R)⟩ := by
  have H := (join0 (join0 (join0 (join0 (phase0 n R) (phase1 n R)) (phase2 n R)) (phase3 n R)) (phase4 n R))
  rw [finalR n R] at H
  rw [show 9+6*n+15+2*n+2=26+8*n by omega] at H
  exact H

theorem canon (n : Nat) (R : List Bool) : run0 table (26+8*n) ⟨5,([false,false,false,false,true]),(rep [true,false] (n)) ++ ([true,false,false,false]) ++ (R)⟩ = some ⟨5,([false,false,false,false,true]),(rep [false,false] (n)) ++ ([false,false,true,false]) ++ (R)⟩ := by
  exact epoch n R

end MCarry


abbrev table := MInit.table
abbrev A : List Bool := [true,false]
abbrev Z : List Bool := [false,false]
def Q (R : List Bool) : Z0 := ⟨5,[false,false,false,false,true],(R)⟩
def family (n : Nat) : Z0 := ⟨4,([false,true,false,false]) ++ (rep [false,false] (n)) ++ ([true]),[]⟩
def carryCost (n : Nat) : Nat := 18+8*n

theorem carry (n : Nat) (R : List Bool) : run0 table (carryCost n) (Q (rep A n ++ Z ++ R)) = some (Q (rep Z n ++ A ++ R)) := by
  cases n with
  | zero => rfl
  | succ n =>
    have h := MCarry.canon n R
    rw [show MCarry.table = table from rfl] at h
    unfold carryCost
    rw [show 18+8*n.succ = 26+8*n by omega]
    rw [rep_succ_snoc A n,rep_succ_snoc Z n]
    simpa only [table,Q,A,Z,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl


def cost (n : Nat) : Nat := (6+2*n) + fillCost carryCost (n+0) + (18+6*n)
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
end M2481

end BB6.Agent11Raw39B0RECounter2481
