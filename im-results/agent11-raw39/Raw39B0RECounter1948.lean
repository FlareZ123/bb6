import Raw39CounterCarry
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent11CounterCarry
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B0RECounter1948
namespace M1948

namespace MInit

-- 1RB0RE_1RC1RE_0RD---_1LD0RA_1RD1LF_1LA0LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,true,3⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 2 ⟨0,[],([true,false,false]) ++ (rep [false,false] (n)) ++ ([true,true,false,false,true,false,false,false,true])⟩ = some ⟨4,([false,true,true]),([false]) ++ (rep [false,false] (n)) ++ ([true,true,false,false,true,false,false,false,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨4,([false]) ++ (L),([false]) ++ ([false,false]) ++ (R)⟩ = some ⟨4,([false]) ++ ([false,false]) ++ (L),([false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨4,([false,true,true]),([false]) ++ (rep [false,false] (n)) ++ ([true,true,false,false,true,false,false,false,true])⟩ = some ⟨4,([false]) ++ (rep [false,false] (n)) ++ ([true,true]),([false,true,true,false,false,true,false,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [false] [false] [false,false] [false,false] 4 local1 n (([true,true])) (([true,true,false,false,true,false,false,false,true]))

theorem finalL (n : Nat) : ([false]) ++ (rep [false,false] (n)) ++ ([true,true]) = ([false]) ++ (rep [false,false] (n)) ++ ([true,true]) := by
  rfl

theorem finalR (n : Nat) : ([false,true,true,false,false,true,false,false,false,true]) = ([false,true,true,false,false,true,false,false,false,true]) := by
  rfl

theorem epoch (n : Nat) : run0 table (2+4*n) ⟨0,[],([true,false,false]) ++ (rep [false,false] (n)) ++ ([true,true,false,false,true,false,false,false,true])⟩ = some ⟨4,([false]) ++ (rep [false,false] (n)) ++ ([true,true]),([false,true,true,false,false,true,false,false,false,true])⟩ := by
  have H := (join0 (phase0 n) (phase1 n))
  rw [show 2+4*n=2+4*n by omega] at H
  exact H

theorem canon (n : Nat) : run0 table (2+4*n) ⟨0,[],([true,false,false]) ++ (rep [false,false] (n)) ++ ([true,true,false,false,true,false,false,false,true])⟩ = some ⟨4,([false]) ++ (rep [false,false] (n)) ++ ([true,true]),([false,true,true,false,false,true,false,false,false,true])⟩ := by
  exact epoch n

end MInit


namespace MFinish

-- 1RB0RE_1RC1RE_0RD---_1LD0RA_1RD1LF_1LA0LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,true,3⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 9 ⟨4,([false]) ++ (rep [true,true] (n)) ++ ([true,true]),([false,true,true,false,false,true,false,false,false,true])⟩ = some ⟨5,([true,true]) ++ (rep [true,true] (n)) ++ ([true,true]),([true,true,false,false,true,false,false,false,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨5,([true,true]) ++ ([true,true]) ++ (L),(R)⟩ = some ⟨5,([true,true]) ++ (L),([false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (2*n) ⟨5,([true,true]) ++ (rep [true,true] (n)) ++ ([true,true]),([true,true,false,false,true,false,false,false,true])⟩ = some ⟨5,([true,true,true,true]),(rep [false,false] (n)) ++ ([true,true,false,false,true,false,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,true] [] [true,true] [false,false] 2 local1 n (([true,true])) (([true,true,false,false,true,false,false,false,true]))

theorem phase2 (n : Nat) : run0 table 5 ⟨5,([true,true,true,true]),(rep [false,false] (n)) ++ ([true,true,false,false,true,false,false,false,true])⟩ = some ⟨0,[],([true,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true,true,false,false,true,false,false,false,true])⟩ := by rfl

theorem finalL (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem finalR (n : Nat) : ([true,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true,true,false,false,true,false,false,false,true]) = ([true,false,false]) ++ (rep [false,false] (n)) ++ ([false,false,true,true,false,false,true,false,false,false,true]) := by
  calc
    _ = ([true,false,false,false]) ++ (rep [false,false] (n)) ++ ([false,true,true,false,false,true,false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,false,false])) (([true,true,false,false,true,false,false,false,true])) [false] false n
    _ = ([true,false,false]) ++ (rep [false,false] (n)) ++ ([false,false,true,true,false,false,true,false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,false])) (([false,true,true,false,false,true,false,false,false,true])) [false] false n

theorem epoch (n : Nat) : run0 table (14+2*n) ⟨4,([false]) ++ (rep [true,true] (n)) ++ ([true,true]),([false,true,true,false,false,true,false,false,false,true])⟩ = some ⟨0,[],([true,false,false]) ++ (rep [false,false] (n)) ++ ([false,false,true,true,false,false,true,false,false,false,true])⟩ := by
  have H := (join0 (join0 (phase0 n) (phase1 n)) (phase2 n))
  rw [finalR n] at H
  rw [show 9+2*n+5=14+2*n by omega] at H
  exact H

theorem eq1r (n : Nat) : ([true,false,false]) ++ (rep [false,false] (n)) ++ ([false,false,true,true,false,false,true,false,false,false,true]) = ([true,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true,true,false,false,true,false,false,false,true]) := by
  calc
    _ = ([true,false,false,false]) ++ (rep [false,false] (n)) ++ ([false,true,true,false,false,true,false,false,false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,false])) (([false,true,true,false,false,true,false,false,false,true])) [false] false n
    _ = ([true,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true,true,false,false,true,false,false,false,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,false,false,false])) (([true,true,false,false,true,false,false,false,true])) [false] false n

theorem canon (n : Nat) : run0 table (14+2*n) ⟨4,([false]) ++ (rep [true,true] (n)) ++ ([true,true]),([false,true,true,false,false,true,false,false,false,true])⟩ = some ⟨0,[],([true,false,false,false,false]) ++ (rep [false,false] (n)) ++ ([true,true,false,false,true,false,false,false,true])⟩ := by
  simpa only [eq1r n] using epoch n

end MFinish


namespace MCarry

-- 1RB0RE_1RC1RE_0RD---_1LD0RA_1RD1LF_1LA0LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,true,3⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

theorem phase0 (n : Nat) (R : List Bool) : run0 table 9 ⟨4,([false]) ++ (rep [true,true] (n)) ++ ([true,true,false,false]) ++ (R),([false,true,true,false,false,true,false,false,false,true])⟩ = some ⟨5,([true,true]) ++ (rep [true,true] (n)) ++ ([true,true,false,false]) ++ (R),([true,true,false,false,true,false,false,false,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 2 ⟨5,([true,true]) ++ ([true,true]) ++ (L),(R)⟩ = some ⟨5,([true,true]) ++ (L),([false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) (R : List Bool) : run0 table (2*n) ⟨5,([true,true]) ++ (rep [true,true] (n)) ++ ([true,true,false,false]) ++ (R),([true,true,false,false,true,false,false,false,true])⟩ = some ⟨5,([true,true,true,true,false,false]) ++ (R),(rep [false,false] (n)) ++ ([true,true,false,false,true,false,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,true] [] [true,true] [false,false] 2 local1 n (([true,true,false,false]) ++ (R)) (([true,true,false,false,true,false,false,false,true]))

theorem phase2 (n : Nat) (R : List Bool) : run0 table 7 ⟨5,([true,true,true,true,false,false]) ++ (R),(rep [false,false] (n)) ++ ([true,true,false,false,true,false,false,false,true])⟩ = some ⟨4,([false,true,true]) ++ (R),([false,false,false]) ++ (rep [false,false] (n)) ++ ([true,true,false,false,true,false,false,false,true])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 4 ⟨4,([false]) ++ (L),([false,false,false]) ++ ([false,false]) ++ (R)⟩ = some ⟨4,([false]) ++ ([false,false]) ++ (L),([false,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) (R : List Bool) : run0 table (4*n) ⟨4,([false,true,true]) ++ (R),([false,false,false]) ++ (rep [false,false] (n)) ++ ([true,true,false,false,true,false,false,false,true])⟩ = some ⟨4,([false]) ++ (rep [false,false] (n)) ++ ([true,true]) ++ (R),([false,false,false,true,true,false,false,true,false,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 4 [false] [false,false,false] [false,false] [false,false] 4 local3 n (([true,true]) ++ (R)) (([true,true,false,false,true,false,false,false,true]))

theorem phase4 (n : Nat) (R : List Bool) : run0 table 4 ⟨4,([false]) ++ (rep [false,false] (n)) ++ ([true,true]) ++ (R),([false,false,false,true,true,false,false,true,false,false,false,true])⟩ = some ⟨4,([false,false,false]) ++ (rep [false,false] (n)) ++ ([true,true]) ++ (R),([false,true,true,false,false,true,false,false,false,true])⟩ := by rfl

theorem finalL (n : Nat) (R : List Bool) : ([false,false,false]) ++ (rep [false,false] (n)) ++ ([true,true]) ++ (R) = ([false]) ++ (rep [false,false] (n)) ++ ([false,false,true,true]) ++ (R) := by
  calc
    _ = ([false,false]) ++ (rep [false,false] (n)) ++ ([false,true,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([true,true]) ++ (R)) [false] false n
    _ = ([false]) ++ (rep [false,false] (n)) ++ ([false,false,true,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,true,true]) ++ (R)) [false] false n

theorem finalR (n : Nat) (R : List Bool) : ([false,true,true,false,false,true,false,false,false,true]) = ([false,true,true,false,false,true,false,false,false,true]) := by
  rfl

theorem epoch (n : Nat) (R : List Bool) : run0 table (20+6*n) ⟨4,([false]) ++ (rep [true,true] (n)) ++ ([true,true,false,false]) ++ (R),([false,true,true,false,false,true,false,false,false,true])⟩ = some ⟨4,([false]) ++ (rep [false,false] (n)) ++ ([false,false,true,true]) ++ (R),([false,true,true,false,false,true,false,false,false,true])⟩ := by
  have H := (join0 (join0 (join0 (join0 (phase0 n R) (phase1 n R)) (phase2 n R)) (phase3 n R)) (phase4 n R))
  rw [finalL n R] at H
  rw [show 9+2*n+7+4*n+4=20+6*n by omega] at H
  exact H

theorem canon (n : Nat) (R : List Bool) : run0 table (20+6*n) ⟨4,([false]) ++ (rep [true,true] (n)) ++ ([true,true,false,false]) ++ (R),([false,true,true,false,false,true,false,false,false,true])⟩ = some ⟨4,([false]) ++ (rep [false,false] (n)) ++ ([false,false,true,true]) ++ (R),([false,true,true,false,false,true,false,false,false,true])⟩ := by
  exact epoch n R

end MCarry


abbrev table := MInit.table
abbrev A : List Bool := [true,true]
abbrev Z : List Bool := [false,false]
def Q (R : List Bool) : Z0 := ⟨4,([false]) ++ (R),[false,true,true,false,false,true,false,false,false,true]⟩
def family (n : Nat) : Z0 := ⟨0,[],([true,false,false]) ++ (rep [false,false] (n)) ++ ([true,true,false,false,true,false,false,false,true])⟩
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

theorem entry : run0 table 61 ⟨0,[],[]⟩ = some (family 0) := by rfl


def cost (n : Nat) : Nat := (2+4*n) + fillCost carryCost (n+0) + (14+2*n)
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := MInit.canon n
  have h2 := fill table Q A Z carryCost carry (n+0) [true,true]
  have h3 := MFinish.canon n
  rw [rep_add Z n 0,rep_add A n 0] at h2
  simp only [Q,A,Z,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] at h2
  have h := join0 (join0 h1 h2) h3
  simpa only [cost,family,rep,rep_succ_snoc,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 61 cost entry (by intro n; unfold cost; omega) growth m hm

#print axioms growth
#print axioms never
end M1948

end BB6.Agent11Raw39B0RECounter1948
