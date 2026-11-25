import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39Counter2391
open BB6Coverage BB6Coverage.Agent31Pump


namespace Init

-- 1RB1RB_1RC1RE_0RD1RB_1LD0RA_1LF---_1LC0LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 14 ⟨1,([false,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([false,false]),[]⟩ = some ⟨5,([true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([false,false]),([true,false,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨5,([true,true,true,true,true,true]) ++ ([true,true,true,true]) ++ (L),(R)⟩ = some ⟨5,([true,true,true,true,true,true]) ++ (L),([false,false,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (4*n) ⟨5,([true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([false,false]),([true,false,true])⟩ = some ⟨5,([true,true,true,true,true,true,false,false]),(rep [false,false,false,false] (n)) ++ ([true,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,true,true,true,true,true] [] [true,true,true,true] [false,false,false,false] 4 local1 n (([false,false])) (([true,false,true]))

theorem phase2 (n : Nat) : run0 table 30 ⟨5,([true,true,true,true,true,true,false,false]),(rep [false,false,false,false] (n)) ++ ([true,false,true])⟩ = some ⟨1,([false,true,false,false]),([true,false,true,false]) ++ (rep [false,false,false,false] (n)) ++ ([true,false,true])⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,false,false]) = ([false,true,false,false]) := by
  rfl

theorem finalR (n : Nat) : ([true,false,true,false]) ++ (rep [false,false,false,false] (n)) ++ ([true,false,true]) = ([true,false,true,false]) ++ (rep [false,false,false,false] (n)) ++ ([true,false,true]) := by
  rfl

theorem epoch (n : Nat) : run0 table (44+4*n) ⟨1,([false,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([false,false]),[]⟩ = some ⟨1,([false,true,false,false]),([true,false,true,false]) ++ (rep [false,false,false,false] (n)) ++ ([true,false,true])⟩ := by
  have H := (join0 (join0 (phase0 n) (phase1 n)) (phase2 n))
  rw [show 14+4*n+30=44+4*n by omega] at H
  exact H

end Init

namespace Carry

-- 1RB1RB_1RC1RE_0RD1RB_1LD0RA_1LF---_1LC0LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

theorem phase0 (n : Nat) (R : List Bool) : run0 table 14 ⟨1,([false,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([false,false]),([false,false,false,false]) ++ (R)⟩ = some ⟨5,([true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([false,false]),([true,false,true,false]) ++ (R)⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨5,([true,true,true,true,true,true]) ++ ([true,true,true,true]) ++ (L),(R)⟩ = some ⟨5,([true,true,true,true,true,true]) ++ (L),([false,false,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) (R : List Bool) : run0 table (4*n) ⟨5,([true,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([false,false]),([true,false,true,false]) ++ (R)⟩ = some ⟨5,([true,true,true,true,true,true,false,false]),(rep [false,false,false,false] (n)) ++ ([true,false,true,false]) ++ (R)⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [true,true,true,true,true,true] [] [true,true,true,true] [false,false,false,false] 4 local1 n (([false,false])) (([true,false,true,false]) ++ (R))

theorem phase2 (n : Nat) (R : List Bool) : run0 table 30 ⟨5,([true,true,true,true,true,true,false,false]),(rep [false,false,false,false] (n)) ++ ([true,false,true,false]) ++ (R)⟩ = some ⟨1,([false,true,false,false]),([true,false,true,false]) ++ (rep [false,false,false,false] (n)) ++ ([true,false,true,false]) ++ (R)⟩ := by rfl

theorem finalL (n : Nat) (R : List Bool) : ([false,true,false,false]) = ([false,true,false,false]) := by
  rfl

theorem finalR (n : Nat) (R : List Bool) : ([true,false,true,false]) ++ (rep [false,false,false,false] (n)) ++ ([true,false,true,false]) ++ (R) = ([true,false,true,false]) ++ (rep [false,false,false,false] (n)) ++ ([true,false,true,false]) ++ (R) := by
  rfl

theorem epoch (n : Nat) (R : List Bool) : run0 table (44+4*n) ⟨1,([false,true,true,true,true,true]) ++ (rep [true,true,true,true] (n)) ++ ([false,false]),([false,false,false,false]) ++ (R)⟩ = some ⟨1,([false,true,false,false]),([true,false,true,false]) ++ (rep [false,false,false,false] (n)) ++ ([true,false,true,false]) ++ (R)⟩ := by
  have H := (join0 (join0 (phase0 n R) (phase1 n R)) (phase2 n R))
  rw [show 14+4*n+30=44+4*n by omega] at H
  exact H

end Carry

abbrev A : List Bool := [true,false,true,false]
abbrev Z : List Bool := [false,false,false,false]
abbrev O : List Bool := [true,true,true,true]
def Q (R : List Bool) : Z0 := ⟨1,[false,true,false,false],R⟩
def F (n : Nat) (R : List Bool) : Z0 := ⟨1,[false,true,true,true,true,true] ++ rep O n ++ [false,false],R⟩

theorem block (L R : List Bool) : run0 Init.table 4 ⟨1,[false]++L,A++R⟩ = some ⟨1,[false]++O++L,R⟩ := by rfl

theorem consume (n : Nat) (R : List Bool) : run0 Init.table (4*(n+1)) (Q (rep A (n+1) ++ R)) = some (F n R) := by
  have h := sweepR Init.table 1 [false] [] A O 4 block (n+1) [true,false,false] R
  simp only [List.nil_append,List.append_assoc] at h
  have eq : rep O (n+1) ++ [true,false,false] = [true,true,true,true,true] ++ rep O n ++ [false,false] := by
    have rot : [true] ++ rep O n = rep O n ++ [true] := rotate true [true,true,true] n
    simp only [rep, List.append_assoc]
    change [true,true,true,true] ++ (rep O n ++ ([true] ++ [false,false])) = _
    rw [← List.append_assoc (rep O n) [true] [false,false], ← rot]
    rfl
  rw [eq] at h
  exact h

theorem carry (n : Nat) (R : List Bool) : run0 Init.table (44+4*n) (F n (Z++R)) = some (Q (A++rep Z n++A++R)) := by
  exact Carry.epoch n R

def T : Nat → Nat
  | 0 => 0
  | n+1 => T n + (4*(n+1)+(44+4*n)) + T n

theorem countUp (n : Nat) (R : List Bool) : run0 Init.table (T n) (Q (A++rep Z n++R)) = some (Q (rep A (n+1)++R)) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have zsplit : rep Z (n+1) = rep Z n ++ Z := by
      rw [rep_snoc]; rfl
    have asplit : rep A (n+2) = rep A (n+1) ++ A := by
      rw [rep_snoc]; rfl
    have h1 : run0 Init.table (T n) (Q (A++rep Z (n+1)++R)) = some (Q (rep A (n+1)++(Z++R))) := by
      rw [zsplit]
      simpa only [List.append_assoc] using ih (Z++R)
    have h2 := consume n (Z++R)
    have h3 := carry n R
    have h4 : run0 Init.table (T n) (Q (A++rep Z n++A++R)) = some (Q (rep A (n+2)++R)) := by
      rw [asplit]
      simpa only [List.append_assoc] using ih (A++R)
    have h := join0 (join0 (join0 h1 h2) h3) h4
    rw [show T n + 4*(n+1)+(44+4*n)+T n = T (n+1) by simp only [T]; omega] at h
    exact h

theorem last4 (L : List Bool) : run0 Init.table 4 ⟨1,[false]++L,[true,false,true]⟩ = some ⟨1,[false]++O++L,[]⟩ := by rfl

theorem finish (n : Nat) : run0 Init.table 4 (F n [true,false,true]) = some (F (n+1) []) := by
  exact last4 ([true,true,true,true,true]++rep O n++[false,false])

def family (n : Nat) : Z0 := F n []
def cost (n : Nat) : Nat := (44+4*n)+T n+4*(n+1)+4

theorem entry : run0 Init.table 25 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 Init.table (cost n) (family n) = some (family (n+1)) := by
  have h1 : run0 Init.table (44+4*n) (family n) = some (Q (A++rep Z n++[true,false,true])) := Init.epoch n
  exact join0 (join0 (join0 h1 (countUp n [true,false,true])) (consume n [true,false,true])) (finish n)

theorem exactCost (n : Nat) : cost n + 4 = 56*2^n := by
  have h : T n + 8*n+56 = 56*2^n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [T, Nat.pow_succ]
      omega
  unfold cost
  omega

theorem never (m : Machine) (hm : compatible Init.table m) : NeverHalts m :=
  never_of_growth Init.table family 25 cost entry (by intro n; unfold cost; omega) growth m hm

#print axioms growth
#print axioms exactCost
#print axioms never


end BB6.Agent11Raw39Counter2391
