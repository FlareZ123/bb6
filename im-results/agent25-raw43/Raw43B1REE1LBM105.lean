import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B1REE1LBM105
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def P : Nat → List Bool
  | 0 => []
  | n+1 => true::false::P n
def Q : Nat → List Bool
  | 0 => []
  | n+1 => false::true::Q n
def W (n : Nat) := List.replicate n true

def F (n : Nat) (R : List Bool) : Z0 := ⟨5,W n,R⟩
def A (n : Nat) (R : List Bool) : Z0 := ⟨0,W n,R⟩
def B (n : Nat) (R : List Bool) : Z0 := ⟨0,false::W n,R⟩

theorem p_push (n : Nat) (R : List Bool) : P n++true::false::R = P (n+1)++R := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [P,List.cons_append]; rw [ih]; rfl

theorem p_shift (n : Nat) (R : List Bool) : false::(P n++R) = Q n++false::R := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [P,Q,List.cons_append]; rw [← ih]

theorem q_shift (n : Nat) (R : List Bool) : true::(Q n++R) = P n++true::R := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [P,Q,List.cons_append]; rw [← ih]

theorem q_push (n : Nat) (R : List Bool) : Q n++false::true::R = Q (n+1)++R := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Q,List.cons_append]; rw [ih]; rfl

theorem f_sweep (n b : Nat) (R : List Bool) :
    run0 table (4*n) (F (2*n+b+1) R) = some (F (b+1) (P n++R)) := by
  induction n generalizing R with
  | zero => simp [F,P,run0]
  | succ n ih =>
    have h : run0 table 4 (F (2*(n+1)+b+1) R) = some (F (2*n+b+1) (true::false::R)) := by
      have he : 2*(n+1)+b+1=(2*n+b+1)+2 := by omega
      rw [he]
      rfl
    have H := join0 h (ih (true::false::R))
    rw [p_push] at H
    simpa only [show 4+4*n=4*(n+1) by omega] using H

theorem f_odd (n : Nat) (R : List Bool) :
    run0 table (4*n+3) (F (2*n+1) R) = some (A 2 (Q n++false::R)) := by
  have h1 := f_sweep n 0 R
  have h2 : run0 table 3 (F 1 (P n++R)) = some (A 2 (false::(P n++R))) := by rfl
  have H := join0 h1 h2
  rw [p_shift] at H
  exact H

theorem a_sweep (n m : Nat) (R : List Bool) :
    run0 table (2*n) (A (m+1) (Q n++R)) = some (A (m+1+2*n) R) := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    have h : run0 table 2 (A (m+1) (Q (n+1)++R)) = some (A ((m+2)+1) (Q n++R)) := by rfl
    have H := join0 h (ih (m+2))
    simpa only [show 2+2*n=2*(n+1) by omega,show m+2+1+2*n=m+1+2*(n+1) by omega] using H

theorem b_start (k : Nat) (U : List Bool) :
    run0 table 3 (B (8*k+7) ([true,false,true]++U)) = some (F (8*k+9) (true::true::U)) := by rfl

theorem a_one (m : Nat) (U : List Bool) :
    run0 table 1 (A (m+1) (true::U)) = some (F (m+2) U) := by rfl

theorem a_end (m : Nat) (U : List Bool) (h : U.headD false=false) :
    run0 table 2 (A (m+1) (false::U)) = some (B (m+2) U.tail) := by
  cases U with
  | nil => rfl
  | cons c U => cases c <;> simp_all <;> rfl

theorem consume (k : Nat) (U : List Bool) (h : U.headD false=false) :
    run0 table (48*k+74) (B (8*k+7) ([true,false,true]++U)) = some (B (8*(k+1)+7) U.tail) := by
  have h1 := b_start k U
  have h2 := f_odd (4*k+4) (true::true::U)
  rw [show 2*(4*k+4)+1=8*k+9 by omega] at h2
  rw [q_push] at h2
  have H := join0 h1 h2
  have h3 := a_sweep (4*k+5) 1 (true::U)
  have H := join0 H h3
  have h4 := a_one (8*k+11) U
  rw [show 1+1+2*(4*k+5)=8*k+12 by omega] at H
  have H := join0 H h4
  have h5 := f_odd (4*k+6) U
  rw [show 2*(4*k+6)+1=8*k+11+2 by omega] at h5
  have H := join0 H h5
  have h6 := a_sweep (4*k+6) 1 (false::U)
  have H := join0 H h6
  rw [show 1+1+2*(4*k+6)=8*k+14 by omega] at H
  have h7 := a_end (8*k+13) U h
  have H := join0 H h7
  simpa only [show 3+(4*(4*k+4)+3)+2*(4*k+5)+1+(4*(4*k+6)+3)+2*(4*k+6)+2=48*k+74 by omega,
    show 8*k+13+2=8*(k+1)+7 by omega] using H

theorem b_empty (k : Nat) :
    run0 table 12 (B (8*k+7) []) = some (F (8*k+8) [true,false,true]) := by rfl

theorem f_even_end (U : List Bool) :
    run0 table 17 (F 2 (true::U)) = some (F 5 U) := by rfl

theorem recycle (k : Nat) :
    run0 table (16*k+58) (B (8*k+7) []) = some (B 7 (P (4*k+3)++[true])) := by
  have h1 := b_empty k
  have h2 := f_sweep (4*k+3) 1 [true,false,true]
  rw [show 2*(4*k+3)+1+1=8*k+8 by omega,p_push] at h2
  rw [← q_shift] at h2
  have H := join0 h1 h2
  have H := join0 H (f_even_end (Q (4*k+4)++[]))
  have H := join0 H (f_odd 2 (Q (4*k+4)++[]))
  have H := join0 H (a_sweep 2 1 (false::(Q (4*k+4)++[])))
  have he : (Q (4*k+4)++[]).headD false=false := by rfl
  have H := join0 H (a_end 5 _ he)
  have ht : (Q (4*k+4)++[]).tail = P (4*k+3)++[true] := by
    change true::(Q (4*k+3)++[]) = _
    rw [q_shift]
  rw [ht] at H
  simpa only [show 12+4*(4*k+3)+17+(4*2+3)+2*2+2=16*k+58 by omega] using H

inductive Inv : Z0 → Prop
  | empty (k : Nat) : Inv (B (8*k+7) [])
  | nonempty (k j : Nat) : Inv (B (8*k+7) (P (2*j+1)++[true]))

theorem stepInv (z : Z0) (h : Inv z) : ∃ t z', 0<t ∧ run0 table t z=some z' ∧ Inv z' := by
  cases h with
  | empty k =>
    refine ⟨16*k+58,_,by omega,recycle k,?_⟩
    have he : 4*k+3=2*(2*k+1)+1 := by omega
    rw [he]
    exact Inv.nonempty 0 (2*k+1)
  | nonempty k j =>
    cases j with
    | zero => exact ⟨48*k+74,_,by omega,consume k [] rfl,Inv.empty (k+1)⟩
    | succ j =>
      have h := consume k (false::(P (2*j+1)++[true])) rfl
      exact ⟨48*k+74,_,by omega,h,Inv.nonempty (k+1) j⟩

theorem start : run0 table 21 ⟨0,[],[]⟩ = some (B 7 []) := by rfl

theorem live (N : Nat) : ∃ t z, N≤t ∧ run0 table t ⟨0,[],[]⟩ = some z ∧ Inv z := by
  induction N with
  | zero => exact ⟨21,_,by omega,start,Inv.empty 0⟩
  | succ N ih =>
    obtain ⟨t,z,ht,hz,hi⟩ := ih
    obtain ⟨a,z',ha,hr,hi'⟩ := stepInv z hi
    exact ⟨t+a,z',by omega,join0 hz hr,hi'⟩

open BB6Coverage.Agent50Zipper

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,hr,_⟩ := live n
  let start : Z := ⟨0,0,[],[]⟩
  have hz : (zrun table t start).map project = some z :=
    (run_project table t start).trans hr
  cases hZ : zrun table t start with
  | none => simp [hZ] at hz
  | some z' =>
    have H := zrun_sound table m hm t start z' hZ
    have hb : embed start = blank := by
      unfold embed blank
      congr 1
      funext x
      unfold atCell start
      split <;> rfl
    rw [hb] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl
#print axioms never
end BB6.Agent25Raw43B1REE1LBM105
