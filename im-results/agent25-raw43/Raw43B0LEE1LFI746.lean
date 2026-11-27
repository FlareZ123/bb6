import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B0LEE1LFI746
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def ones (n : Nat) := List.replicate n true
def zeros (n : Nat) := List.replicate n false
def d0 : List Bool := [false,false,false,false,false]
def d1 : List Bool := [false,true,false,true,false]
def d2 : List Bool := [false,false,false,false,true]
def d3 : List Bool := [false,true,false,true,true]
def short : List Bool := [false,true,false,true]
def A (k : Nat) (W : List Bool) : Z0 := ⟨0,false::(ones (5*k)++[false]),W.tail⟩
def F (n : Nat) (R : List Bool) : Z0 := ⟨5,ones n++[false],R⟩

theorem zero_comm (n : Nat) (R : List Bool) : zeros n++false::R = false::(zeros n++R) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [zeros,List.replicate_succ,List.cons_append] at *; rw [ih]

theorem tail_zero (n : Nat) (R : List Bool) : (zeros n++false::R).tail = zeros n++R := by
  rw [zero_comm]; rfl

theorem f_sweep (n : Nat) (R : List Bool) :
    run0 table n (F n R) = some (F 0 (zeros n++R)) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h : run0 table 1 (F (n+1) R) = some (F n (false::R)) := by rfl
    have H := join0 h (ih (false::R))
    rw [zero_comm] at H
    simpa only [show 1+n=n+1 by omega,zeros,List.replicate_succ,List.cons_append] using H

theorem reset (n : Nat) (R : List Bool) :
    run0 table (n+2) (F (n+1) R) = some ⟨0,[false,false],zeros n++R⟩ := by
  have h := f_sweep (n+1) R
  have g : run0 table 1 (F 0 (zeros (n+1)++R)) = some ⟨0,[false,false],zeros n++R⟩ := by rfl
  have H := join0 h g
  simpa only [show (n+1)+1=n+2 by omega] using H

theorem reset0 (k : Nat) (R : List Bool) :
    run0 table (5*k+10) (A k (d0++R)) = some (A 0 (zeros (5*k)++(d1++R))) := by
  have h : run0 table 8 (A k (d0++R)) = some (F (5*k+1) (d1.tail++R)) := by rfl
  have H := join0 h (reset (5*k) (d1.tail++R))
  simpa only [show 8+(5*k+2)=5*k+10 by omega,A,ones,Nat.mul_zero,List.replicate_zero,List.nil_append,d1,List.cons_append,List.tail_cons,tail_zero,List.append_assoc] using H

theorem reset2 (k : Nat) (R : List Bool) :
    run0 table (5*k+10) (A k (d2++R)) = some (A 0 (zeros (5*k)++(d3++R))) := by
  have h : run0 table 8 (A k (d2++R)) = some (F (5*k+1) (d3.tail++R)) := by rfl
  have H := join0 h (reset (5*k) (d3.tail++R))
  simpa only [show 8+(5*k+2)=5*k+10 by omega,A,ones,Nat.mul_zero,List.replicate_zero,List.nil_append,d3,List.cons_append,List.tail_cons,tail_zero,List.append_assoc] using H

theorem resetNil (k : Nat) :
    run0 table (5*k+10) (A k []) = some (A 0 (zeros (5*k)++short)) := by
  have h : run0 table 8 (A k []) = some (F (5*k+1) short.tail) := by rfl
  have H := join0 h (reset (5*k) short.tail)
  simpa only [show 8+(5*k+2)=5*k+10 by omega,A,ones,Nat.mul_zero,List.replicate_zero,List.nil_append,short,List.tail_cons,tail_zero] using H

theorem reset1 (k : Nat) (R : List Bool) :
    run0 table (5*k+12) (A k (d1++R)) = some (A 0 (zeros (5*k)++(d2++R))) := by
  have h : run0 table 7 (A k (d1++R)) = some (F (5*k+4) (true::R)) := by rfl
  have H := join0 h (reset (5*k+3) (true::R))
  have he : zeros (5*k+3) = zeros (5*k)++[false,false,false] := by
    exact (List.replicate_append_replicate (n := 5*k) (m := 3) (a := false)).symm
  rw [he] at H
  simpa only [show 7+(5*k+3+2)=5*k+12 by omega,A,ones,Nat.mul_zero,List.replicate_zero,List.nil_append,d2,List.cons_append,List.tail_cons,tail_zero,List.append_assoc] using H

theorem resetShort (k : Nat) :
    run0 table (5*k+12) (A k short) = some (A 0 (zeros (5*k)++d2)) := by
  have h : run0 table 7 (A k short) = some (F (5*k+4) [true]) := by rfl
  have H := join0 h (reset (5*k+3) [true])
  have he : zeros (5*k+3) = zeros (5*k)++[false,false,false] := by
    exact (List.replicate_append_replicate (n := 5*k) (m := 3) (a := false)).symm
  rw [he] at H
  simpa only [show 7+(5*k+3+2)=5*k+12 by omega,A,ones,Nat.mul_zero,List.replicate_zero,List.nil_append,d2,List.cons_append,List.tail_cons,tail_zero,List.append_assoc] using H

theorem carry (k : Nat) (R : List Bool) (h : R.headD false=false) :
    run0 table 7 (A k (d3++R)) = some (A (k+1) R) := by
  cases R with
  | nil => rfl
  | cons a R => cases a <;> simp_all <;> rfl

inductive Word : List Bool → Prop
  | nil : Word []
  | short : Word short
  | digit0 (R : List Bool) : Word R → Word (d0++R)
  | digit1 (R : List Bool) : Word R → Word (d1++R)
  | digit2 (R : List Bool) : Word R → Word (d2++R)
  | digit3 (R : List Bool) : Word R → Word (d3++R)

theorem head_word (R : List Bool) (h : Word R) : R.headD false=false := by
  cases h <;> rfl

theorem push_zero (k : Nat) (R : List Bool) (h : Word R) : Word (zeros (5*k)++R) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    have he : zeros (5*(k+1)) = d0++zeros (5*k) := by
      rw [show 5*(k+1)=5+5*k by omega]
      exact (List.replicate_append_replicate (n := 5) (m := 5*k) (a := false)).symm
    rw [he,List.append_assoc]
    exact Word.digit0 _ ih

inductive Inv : Z0 → Prop
  | word (k : Nat) (R : List Bool) : Word R → Inv (A k R)

theorem stepInv (z : Z0) (h : Inv z) : ∃ t z', 0<t ∧ run0 table t z=some z' ∧ Inv z' := by
  cases h with
  | word k R h =>
    cases h with
    | nil => exact ⟨5*k+10,_,by omega,resetNil k,Inv.word 0 _ (push_zero k _ Word.short)⟩
    | short => exact ⟨5*k+12,_,by omega,resetShort k,Inv.word 0 _ (push_zero k _ (Word.digit2 _ Word.nil))⟩
    | digit0 R h => exact ⟨5*k+10,_,by omega,reset0 k R,Inv.word 0 _ (push_zero k _ (Word.digit1 _ h))⟩
    | digit1 R h => exact ⟨5*k+12,_,by omega,reset1 k R,Inv.word 0 _ (push_zero k _ (Word.digit2 _ h))⟩
    | digit2 R h => exact ⟨5*k+10,_,by omega,reset2 k R,Inv.word 0 _ (push_zero k _ (Word.digit3 _ h))⟩
    | digit3 R h => exact ⟨7,_,by omega,carry k R (head_word R h),Inv.word (k+1) _ h⟩

theorem start : run0 table 10 ⟨0,[],[]⟩ = some (A 0 short) := by rfl
theorem live (N : Nat) : ∃ t z, N≤t ∧ run0 table t ⟨0,[],[]⟩ = some z ∧ Inv z := by
  induction N with
  | zero => exact ⟨10,_,by omega,start,Inv.word 0 _ Word.short⟩
  | succ N ih =>
    obtain ⟨t,z,ht,hz,hi⟩ := ih
    obtain ⟨a,z',ha,hr,hi'⟩ := stepInv z hi
    exact ⟨t+a,z',by omega,join0 hz hr,hi'⟩

open BB6Coverage.Agent50Zipper
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,hr,_⟩ := live n
  let s : Z := ⟨0,0,[],[]⟩
  have hz : (zrun table t s).map project = some z :=
    (run_project table t s).trans hr
  cases hZ : zrun table t s with
  | none => simp [hZ] at hz
  | some z' =>
    have H := zrun_sound table m hm t s z' hZ
    have hb : embed s = blank := BB6Coverage.Agent31Pump.start_embed
    rw [hb] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl
#print axioms live
#print axioms never
end BB6.Agent25Raw43B0LEE1LFI746
