import SweepPumping

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent7D100Delayed
open BB6Coverage BB6Coverage.Agent31Pump

/-- 1RB1LA_1RC1LE_0RD1RF_0LD0LA_---0LB_1LD1RB -/
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨false,false,3⟩)
  | 3,true  => some (some ⟨false,false,0⟩)
  | 4,true  => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,3⟩)
  | 5,true  => some (some ⟨true,true,1⟩)
  | _,_ => none

def U (n : Nat) : List Bool := rep [true] n
def Z (n : Nat) : List Bool := rep [false] n
def V : List Bool := [true,false,true,false]
def W : List Bool := [false,true]

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

theorem U_push (n : Nat) (R : List Bool) : U n ++ true::R = true::U n ++ R := by
  have h := congrArg (fun x : List Bool => x++R) (rep_snoc [true] n)
  simpa only [U,List.append_assoc,List.cons_append,List.nil_append] using h

theorem W_rotate (j : Nat) : rep W (2*j) ++ [false] = false::rep V j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show 2*(j+1)=2*j+2 by omega]
    simp only [rep,List.append_assoc]
    rw [ih]
    rfl

theorem W_out (j : Nat) (R : List Bool) :
    rep W (2*j+3) ++ R = false::rep V (j+1) ++ true::R := by
  rw [show 2*j+3 = 2*(j+1)+1 by omega,rep_add]
  have h := congrArg (fun x : List Bool => x++true::R) (W_rotate (j+1))
  simpa only [rep,W,List.append_assoc,List.cons_append,List.nil_append] using h

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

theorem BE_one (L R : List Bool) :
    run0 table 2 ⟨1,U 2++L,R⟩ = some ⟨1,L,W++R⟩ := by rfl

theorem BE_all (n : Nat) (L R : List Bool) :
    run0 table (2*n) ⟨1,U (2*n)++L,R⟩ = some ⟨1,L,rep W n++R⟩ := by
  have h := sweepL table 1 [] [] (U 2) W 2 BE_one n L R
  simpa only [List.nil_append,U_block] using h

theorem turn4 (L R : List Bool) :
    run0 table 6 ⟨2,false::L,[true,true,true,true]++R⟩ =
    some ⟨1,U 5++L,R⟩ := by rfl

theorem consume (j : Nat) (R : List Bool) :
    run0 table (12*j+13) (B j ([true,true,true,true]++R)) =
    some (B (j+1) (true::R)) := by
  have h := join0 (scan j ([true,true,true,true]++R)) (turn4 (U (4*j+1)) R)
  rw [← U_add,show 5+(4*j+1)=2*(2*j+3) by omega] at h
  have k := BE_all (2*j+3) [] R
  have H := join0 h (by simpa only [List.append_nil] using k)
  rw [show 12*j+13=1+8*j+6+2*(2*j+3) by omega]
  simpa only [B,W_out] using H

def loopCost (j a : Nat) : Nat := 12*j*a + 6*a*a + 7*a

theorem loopCost_succ (j a : Nat) :
    loopCost j (a+1) = (12*j+13)+loopCost (j+1) a := by
  simp only [loopCost,Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul,Nat.mul_assoc]
  omega

theorem consume_many (j a : Nat) (R : List Bool) :
    run0 table (loopCost j a) (B j (U (3*a)++true::R)) =
    some (B (j+a) (true::R)) := by
  induction a generalizing j with
  | zero => simp only [loopCost,Nat.mul_zero,Nat.zero_add,Nat.add_zero,U,rep,List.nil_append,run0]
  | succ a ih =>
    have h := consume j (U (3*a)++R)
    have g := ih (j+1)
    rw [U_push] at g
    have H := join0 h g
    rw [loopCost_succ,show j+(a+1)=j+1+a by omega,
      show 3*(a+1)=3+3*a by omega,U_add]
    rw [List.append_assoc,U_push]
    exact H

theorem A_first (R : List Bool) :
    run0 table 3 ⟨0,[],true::R⟩ = some (B 0 (true::R)) := by rfl

def scanCost (j : Nat) : Nat := 3+loopCost 0 j+(1+8*j)

theorem epoch_scan (j a : Nat) (S : List Bool) :
    run0 table (scanCost j) ⟨0,[],U (3*j+a+1)++S⟩ =
    some ⟨2,false::U (4*j+1),U (a+1)++S⟩ := by
  have h := A_first (U (3*j+a)++S)
  have g := consume_many 0 j (U a++S)
  have hr : U (3*j)++true::(U a++S) = true::(U (3*j+a)++S) := by
    calc
      _ = true::(U (3*j)++(U a++S)) := U_push (3*j) (U a++S)
      _ = _ := by rw [U_add,List.append_assoc]
  rw [hr] at g
  have H := join0 h (by simpa only [Nat.zero_add] using g)
  have H' := join0 H (scan j (U (a+1)++S))
  exact H'

theorem A_one (L R : List Bool) :
    run0 table 1 ⟨0,[true]++L,R⟩ = some ⟨0,L,[true]++R⟩ := by rfl

theorem A_all (n : Nat) (R : List Bool) :
    run0 table n ⟨0,U n,R⟩ = some ⟨0,[],U n++R⟩ := by
  have h := sweepL table 0 [] [] [true] [true] 1 A_one n [] R
  simpa only [Nat.one_mul,List.nil_append,List.append_nil,U] using h

def A (n k z : Nat) : Z0 := ⟨0,[],U n++(false::(U k++Z z))⟩

theorem epoch (j a k z k' z' d p : Nat)
    (h : ∀ L, run0 table d ⟨2,false::L,U (a+1)++(false::(U k++Z z))⟩ =
      some ⟨0,U p++L,false::(U k'++Z z')⟩) :
    run0 table (scanCost j+d+(p+(4*j+1))) (A (3*j+a+1) k z) =
    some (A (p+(4*j+1)) k' z') := by
  have g := join0 (epoch_scan j a (false::(U k++Z z))) (h (U (4*j+1)))
  rw [← U_add] at g
  exact join0 g (A_all (p+(4*j+1)) (false::(U k'++Z z')))

theorem BE_last (R : List Bool) :
    run0 table 1 ⟨1,[true],R⟩ = some ⟨4,[],true::R⟩ := by rfl

theorem odd_end (a : Nat) (R : List Bool) :
    run0 table (2*a+1) ⟨1,U (2*a+1),R⟩ =
    some ⟨4,[],true::rep W a++R⟩ := by
  rw [U_add]
  exact join0 (BE_all a [true] R) (BE_last (rep W a++R))

theorem turn_hole (L R : List Bool) :
    run0 table 9 ⟨2,false::L,[true,true,true,false,true,true,true]++R⟩ =
    some ⟨1,U 8++L,R⟩ := by rfl

theorem lastEpoch (j : Nat) (R : List Bool) :
    run0 table (scanCost j+9+(4*j+9)) ⟨0,[],U (3*j+3)++false::true::true::true::R⟩ =
    some ⟨4,[],true::rep W (2*j+4)++R⟩ := by
  have h := epoch_scan j 2 (false::true::true::true::R)
  have g := turn_hole (U (4*j+1)) R
  have H := join0 h g
  rw [← U_add,show 8+(4*j+1)=2*(2*j+4)+1 by omega] at H
  rw [show 4*j+9=2*(2*j+4)+1 by omega]
  exact join0 H (odd_end (2*j+4) R)

#print axioms consume_many
#print axioms epoch
#print axioms lastEpoch
end BB6.Agent7D100Delayed
