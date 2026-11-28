import SweepPumping
import Run0LastHole

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent7D100FiniteF1
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent13BlankDelay

/-- 1RB1LA_1RC1LE_0RD1RE_0LD0LA_1RF0LB_1LD--- -/
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨false,false,3⟩)
  | 3,true  => some (some ⟨false,false,0⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true  => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,3⟩)
  | _,_ => none

def U (n : Nat) : List Bool := rep [true] n
def V : List Bool := [true,false,true,false]
def W : List Bool := [true,false]

theorem rep_add (P : List Bool) (a b : Nat) : rep P (a+b) = rep P a ++ rep P b := by
  induction a with
  | zero => simp [rep]
  | succ a ih =>
    rw [show a+1+b=a+b+1 by omega]
    simp only [rep,ih,List.append_assoc]

theorem U_add (a b : Nat) : U (a+b) = U a ++ U b := rep_add [true] a b

theorem U_block (k n : Nat) : rep (U k) n = U (k*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ,Nat.add_comm (k*n) k,U_add]
    simp only [rep,ih]

theorem W_twice (j : Nat) : rep W (2*j) = rep V j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show 2*(j+1)=2*j+2 by omega,Nat.add_comm (2*j) 2,rep_add,ih]
    rfl

def B (j : Nat) (R : List Bool) : Z0 := ⟨1,[],false::rep V j++R⟩

theorem scan_first (j : Nat) (R : List Bool) :
    run0 table 1 (B j R) = some ⟨2,[false]++[true],rep V j++R⟩ := by rfl

theorem scan_one (L R : List Bool) :
    run0 table 8 ⟨2,[false]++L,V++R⟩ = some ⟨2,[false]++U 4++L,R⟩ := by rfl

theorem scan (j : Nat) (R : List Bool) :
    run0 table (1+8*j) (B j R) = some ⟨2,false::U (4*j+1),R⟩ := by
  have h := scan_first j R
  have g := sweepR table 2 [false] [] V (U 4) 8 scan_one j [true] R
  have H := join0 h (by simpa only [List.nil_append] using g)
  rw [U_add,show U 1 = [true] by rfl]
  simpa only [List.nil_append,List.cons_append,U_block] using H

theorem EB_one (L R : List Bool) :
    run0 table 2 ⟨4,U 2++L,R⟩ = some ⟨4,L,W++R⟩ := by rfl

theorem EB_all (n : Nat) (L R : List Bool) :
    run0 table (2*n) ⟨4,U (2*n)++L,R⟩ = some ⟨4,L,rep W n++R⟩ := by
  have h := sweepL table 4 [] [] (U 2) W 2 EB_one n L R
  simpa only [List.nil_append,U_block] using h

theorem turn3 (L R : List Bool) :
    run0 table 5 ⟨2,false::L,[true,true,true]++R⟩ = some ⟨4,U 4++L,R⟩ := by rfl

theorem EB_last (R : List Bool) :
    run0 table 1 ⟨4,[true],R⟩ = some ⟨1,[],false::R⟩ := by rfl

theorem consume (j : Nat) (R : List Bool) :
    run0 table (12*j+11) (B j ([true,true,true]++R)) = some (B (j+1) R) := by
  have h := join0 (scan j ([true,true,true]++R)) (turn3 (U (4*j+1)) R)
  rw [← U_add,show 4+(4*j+1)=2*(2*(j+1))+1 by omega,U_add,show U 1=[true] by rfl] at h
  have g := join0 h (EB_all (2*(j+1)) [true] R)
  have H := join0 g (EB_last (rep W (2*(j+1))++R))
  rw [show 12*j+11=1+8*j+5+2*(2*(j+1))+1 by omega]
  simpa only [B,W_twice,List.cons_append] using H

def loopCost (j a : Nat) : Nat := 12*j*a+6*a*a+5*a

theorem loopCost_succ (j a : Nat) : loopCost j (a+1) = (12*j+11)+loopCost (j+1) a := by
  simp only [loopCost,Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul,Nat.mul_assoc]
  omega

theorem consume_many (j a : Nat) (R : List Bool) :
    run0 table (loopCost j a) (B j (U (3*a)++R)) = some (B (j+a) R) := by
  induction a generalizing j with
  | zero => simp only [loopCost,Nat.mul_zero,Nat.zero_add,Nat.add_zero,U,rep,List.nil_append,run0]
  | succ a ih =>
    have H := join0 (consume j (U (3*a)++R)) (ih (j+1))
    rw [loopCost_succ,show j+(a+1)=j+1+a by omega,show 3*(a+1)=3+3*a by omega,U_add,List.append_assoc]
    exact H

theorem A_first (R : List Bool) :
    run0 table 3 ⟨0,[],true::R⟩ = some (B 0 (true::R)) := by rfl

def A (n : Nat) (S : List Bool) : Z0 := ⟨0,[],U n++S⟩
def scanCost (j : Nat) : Nat := 3+loopCost 0 j+(1+8*j)

theorem epoch_scan (j r : Nat) (S : List Bool) (hn : 0 < 3*j+r) :
    run0 table (scanCost j) (A (3*j+r) S) = some ⟨2,false::true::U (4*j),U r++S⟩ := by
  have hn' : 3*j+r = 1+(3*j+r-1) := by omega
  have h : run0 table 3 (A (3*j+r) S) = some (B 0 (U (3*j+r)++S)) := by
    rw [hn',A,U_add,List.append_assoc,show U 1=[true] by rfl]
    exact A_first (U (3*j+r-1)++S)
  have g := consume_many 0 j (U r++S)
  rw [← List.append_assoc,← U_add,Nat.zero_add] at g
  have H := join0 (join0 h g) (scan j (U r++S))
  rw [show 4*j+1=1+4*j by omega,U_add,show U 1=[true] by rfl] at H
  exact H

theorem A_one (L R : List Bool) :
    run0 table 1 ⟨0,[true]++L,R⟩ = some ⟨0,L,[true]++R⟩ := by rfl

theorem A_all (n : Nat) (R : List Bool) :
    run0 table n ⟨0,U n,R⟩ = some (A n R) := by
  have h := sweepL table 0 [] [] [true] [true] 1 A_one n [] R
  simpa only [Nat.one_mul,List.nil_append,List.append_nil,U,A] using h

theorem epoch (j r p d : Nat) (S S' : List Bool) (hn : 0 < 3*j+r)
    (h : ∀ L, run0 table d ⟨2,false::true::L,U r++S⟩ = some ⟨0,U p++L,S'⟩) :
    run0 table (scanCost j+d+(4*j+p)) (A (3*j+r) S) = some (A (4*j+p) S') := by
  have H := join0 (epoch_scan j r S hn) (h (U (4*j)))
  rw [← U_add,Nat.add_comm p (4*j)] at H
  exact join0 H (A_all (4*j+p) S')

#print axioms consume_many
#print axioms epoch_scan
#print axioms epoch
end BB6.Agent7D100FiniteF1
