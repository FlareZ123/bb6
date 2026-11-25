import SweepPumping
import Raw58Live

namespace BB6Coverage.Agent4Raw109LA142
open Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,true,1⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def O (n : Nat) := List.replicate n true
def Z (n : Nat) := List.replicate n false
def F (b : Bool) (k : Nat) (R : List Bool) : Z0 :=
  ⟨5,b::(Z (3*k+1) ++ [true,true]),R⟩
inductive Code : List Bool → Prop where
  | nil : Code []
  | two : Code [true,true]
  | digit (b : Bool) (R : List Bool) : Code R → Code (true::true::b::R)

theorem prefixCode (k : Nat) (R : List Bool) (h : Code R) :
    Code (O (3*k) ++ R) := by
  induction k with
  | zero => exact h
  | succ k ih => exact Code.digit true _ ih

theorem carry (k : Nat) (b : Bool) (R : List Bool) :
    run0 table 3 (F false k (true::true::b::R)) = some (F b (k+1) R) := by rfl
theorem carryEnd (k : Nat) :
    run0 table 3 (F false k [true,true]) = some (F false (k+1) []) := by rfl

theorem scan (n : Nat) (R : List Bool) :
    run0 table n ⟨3,Z n ++ [true,true],R⟩ =
      some ⟨3,[true,true],O n ++ R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h1 : run0 table 1 ⟨3,Z (n+1) ++ [true,true],R⟩ =
      some ⟨3,Z n ++ [true,true],true::R⟩ := by rfl
    have H := join0 h1 (ih (true::R))
    rw [Nat.add_comm 1 n] at H
    have he : O (n+1) ++ R = O n ++ true::R := by
      simp only [O,List.replicate_succ',List.append_assoc,List.singleton_append]
    rw [he]
    exact H

theorem reset (n : Nat) (R : List Bool) :
    run0 table ((n+3)+4) ⟨3,Z (n+3) ++ [true,true],R⟩ =
      some (F false 0 (O (n+1) ++ R)) := by
  have h1 := scan (n+3) R
  have h2 : run0 table 4 ⟨3,[true,true],O (n+3) ++ R⟩ =
      some (F false 0 (O (n+1) ++ R)) := by rfl
  exact join0 h1 h2

theorem clear (k : Nat) (R : List Bool) :
    run0 table (1+((3*k+1+3)+4)) (F true (k+1) R) =
      some (F false 0 (O (3*k) ++ true::true::false::R)) := by
  have h1 : run0 table 1 (F true (k+1) R) =
      some ⟨3,Z (3*k+1+3) ++ [true,true],false::R⟩ := by rfl
  have H := join0 h1 (reset (3*k+1) (false::R))
  have he : O (3*k+1+1) ++ false::R = O (3*k) ++ true::true::false::R := by
    simp only [O,List.replicate_succ',List.append_assoc,List.singleton_append]
    rfl
  rw [he] at H
  exact H

theorem overflow (k : Nat) :
    run0 table (2+((3*k+1+3)+4)) (F false k []) =
      some (F false 0 (O (3*k) ++ [true,true])) := by
  have h1 : run0 table 2 (F false k []) =
      some ⟨3,Z (3*k+1+3) ++ [true,true],[]⟩ := by rfl
  have H := join0 h1 (reset (3*k+1) [])
  have he : O (3*k+1+1) ++ [] = O (3*k) ++ [true,true] := by
    simp only [O,List.replicate_succ',List.append_assoc,List.singleton_append,List.append_nil]
  rw [he] at H
  exact H

theorem progress (R : List Bool) (h : Code R) (k : Nat) :
    ∃ t S, 0<t ∧ run0 table t (F false k R) = some (F false 0 S) ∧ Code S := by
  induction h generalizing k with
  | nil => exact ⟨_,_,by omega,overflow k,prefixCode k _ Code.two⟩
  | two =>
    exact ⟨_,_,by omega,join0 (carryEnd k) (overflow (k+1)),prefixCode (k+1) _ Code.two⟩
  | digit b R h ih =>
    cases b with
    | true =>
      exact ⟨_,_,by omega,join0 (carry k true R) (clear k R),prefixCode k _ (Code.digit false R h)⟩
    | false =>
      obtain ⟨t,S,ht,hr,hS⟩ := ih (k+1)
      exact ⟨3+t,S,by omega,join0 (carry k false R) hr,hS⟩

theorem entry : run0 table 9 ⟨0,[],[]⟩ = some (F false 0 []) := by rfl
theorem arbitrary (n : Nat) :
    ∃ t ≥ n, ∃ z, run0 table t ⟨0,[],[]⟩ = some z := by
  have h : ∀ k : Nat, ∃ t ≥ k, ∃ R, Code R ∧ run0 table t ⟨0,[],[]⟩ = some (F false 0 R) := by
    intro k
    induction k with
    | zero => exact ⟨9,by omega,[],Code.nil,entry⟩
    | succ k ih =>
      obtain ⟨t,ht,R,hR,hr⟩ := ih
      obtain ⟨u,S,hu,hs,hS⟩ := progress R hR 0
      exact ⟨t+u,by omega,S,hS,join0 hr hs⟩
  obtain ⟨t,ht,R,_,hr⟩ := h n
  exact ⟨t,ht,F false 0 R,hr⟩
#print axioms arbitrary

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table (fun n => by
    obtain ⟨t,ht,z,hr⟩ := arbitrary n
    exact ⟨t,z,ht,hr⟩) m hm
#print axioms never
end BB6Coverage.Agent4Raw109LA142
