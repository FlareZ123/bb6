import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B1REE1RCM174
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | _,_ => none

def P : Nat → List Bool
  | 0 => []
  | n+1 => false::false::true::P n

def R (k : Nat) : List Bool := P k++[false,true]
def A (L : List Bool) (k : Nat) : Z0 := ⟨0,L,R k⟩
def D (X : List Bool) (k : Nat) : Z0 := ⟨3,true::X,R k⟩

theorem pushP (k : Nat) (X : List Bool) : P k++false::false::true::X = P (k+1)++X := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [P,List.cons_append]; rw [ih]; rfl

theorem d_return (k : Nat) (X : List Bool) :
    run0 table (3*k+6) (D X k) = some (A (P k++false::X) 0) := by
  induction k generalizing X with
  | zero => rfl
  | succ k ih =>
    have h : run0 table 3 (D X (k+1)) = some (D (false::true::false::X) k) := by rfl
    have H := join0 h (ih (false::true::false::X))
    rw [pushP] at H
    simpa only [show 3+(3*k+6)=3*(k+1)+6 by omega] using H

theorem zero (k : Nat) (X : List Bool) :
    run0 table (3*k+6) (A (false::X) k) = some (A (P k++true::X) 0) := by
  cases k with
  | zero => rfl
  | succ k =>
    have h : run0 table 3 (A (false::X) (k+1)) = some (D (false::true::true::X) k) := by rfl
    have H := join0 h (d_return k (false::true::true::X))
    rw [pushP] at H
    simpa only [show 3+(3*k+6)=3*(k+1)+6 by omega] using H

theorem one (k : Nat) (X : List Bool) :
    run0 table (3*k+10) (A (true::false::true::X) k) = some (A (P k++false::false::false::X) 0) := by
  have h : run0 table 4 (A (true::false::true::X) k) = some (D (false::false::X) k) := by rfl
  have H := join0 h (d_return k (false::false::X))
  simpa only [show 4+(3*k+6)=3*k+10 by omega] using H

theorem carry (k : Nat) (X : List Bool) :
    run0 table 3 (A (true::false::false::X) k) = some (A X (k+1)) := by rfl
theorem last (k : Nat) : run0 table 3 (A [true] k) = some (A [] (k+1)) := by rfl
theorem rebuild (k : Nat) :
    run0 table (3*k+6) (A [] k) = some (A (P k++[true]) 0) := by
  cases k with
  | zero => rfl
  | succ k =>
    have h : run0 table 3 (A [] (k+1)) = some (D [false,true,true] k) := by rfl
    have H := join0 h (d_return k [false,true,true])
    rw [pushP] at H
    simpa only [show 3+(3*k+6)=3*(k+1)+6 by omega] using H

inductive LWord : List Bool → Prop
  | nil : LWord []
  | last : LWord [true]
  | d0 (X : List Bool) : LWord X → LWord (false::false::true::X)
  | d1 (X : List Bool) : LWord X → LWord (true::false::true::X)
  | d2 (X : List Bool) : LWord X → LWord (false::false::false::X)
  | d3 (X : List Bool) : LWord X → LWord (true::false::false::X)

theorem wordPush (k : Nat) (X : List Bool) (h : LWord X) : LWord (P k++X) := by
  induction k with
  | zero => exact h
  | succ k ih => exact LWord.d0 _ ih

inductive Inv : Z0 → Prop
  | word (k : Nat) (X : List Bool) : LWord X → Inv (A X k)

theorem stepInv (z : Z0) (h : Inv z) : ∃ t z', 0<t ∧ run0 table t z=some z' ∧ Inv z' := by
  cases h with
  | word k X h =>
    cases h with
    | nil => exact ⟨3*k+6,_,by omega,rebuild k,Inv.word 0 _ (wordPush k _ LWord.last)⟩
    | last => exact ⟨3,_,by omega,last k,Inv.word (k+1) _ LWord.nil⟩
    | d0 X h => exact ⟨3*k+6,_,by omega,zero k (false::true::X),Inv.word 0 _ (wordPush k _ (LWord.d1 _ h))⟩
    | d1 X h => exact ⟨3*k+10,_,by omega,one k X,Inv.word 0 _ (wordPush k _ (LWord.d2 _ h))⟩
    | d2 X h => exact ⟨3*k+6,_,by omega,zero k (false::false::X),Inv.word 0 _ (wordPush k _ (LWord.d3 _ h))⟩
    | d3 X h => exact ⟨3,_,by omega,carry k X,Inv.word (k+1) _ h⟩

theorem start : run0 table 23 ⟨0,[],[]⟩ = some (A [] 2) := by rfl
theorem live (N : Nat) : ∃ t z, N≤t ∧ run0 table t ⟨0,[],[]⟩ = some z ∧ Inv z := by
  induction N with
  | zero => exact ⟨23,_,by omega,start,Inv.word 2 _ LWord.nil⟩
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
end BB6.Agent25Raw43B1REE1RCM174
