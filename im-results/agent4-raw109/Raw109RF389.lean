import SweepPumping
import Raw58Live

namespace BB6Coverage.Agent4Raw109RF389
open Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,true,1⟩)
  | 5,false => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def O (n : Nat) := List.replicate n true
def Z (n : Nat) := List.replicate n false

theorem scanC (n : Nat) (L : List Bool) :
    run0 table n ⟨2,true::L,O n⟩ = some ⟨2,true::(Z n ++ L),[]⟩ := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have h1 : run0 table 1 ⟨2,true::L,O (n+1)⟩ = some ⟨2,true::false::L,O n⟩ := by rfl
    have h := join0 h1 (ih (false::L))
    simpa only [Nat.add_comm 1 n,Z,List.replicate_succ',List.append_assoc,List.singleton_append] using h

theorem scanD (n : Nat) (L R : List Bool) :
    run0 table n ⟨3,Z n ++ L,R⟩ = some ⟨3,L,O n ++ R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h1 : run0 table 1 ⟨3,Z (n+1) ++ L,R⟩ = some ⟨3,Z n ++ L,true::R⟩ := by rfl
    have h := join0 h1 (ih (true::R))
    simpa only [Nat.add_comm 1 n,O,List.replicate_succ',List.append_assoc,List.singleton_append] using h

def A (n : Nat) : Z0 := ⟨0,[],false::O n⟩
def C (k : Nat) (L : List Bool) : Z0 := ⟨2,Z (k+1) ++ true::L,[]⟩

theorem enter (n : Nat) :
    run0 table (2+n+1) (A (n+1)) = some (C (n+1) [true]) := by
  have h := scanC n [true,true]
  have h1 : run0 table 2 (A (n+1)) = some ⟨2,[true,true,true],O n⟩ := by rfl
  have h2 : run0 table 1 ⟨2,true::(Z n ++ [true,true]),[]⟩ =
      some (C (n+1) [true]) := by rfl
  exact join0 (join0 h1 h) h2

theorem stepC (k : Nat) (L : List Bool) :
    run0 table (2*k+10) (C (k+1) L) = some (C k (true::true::true::L)) := by
  cases k with
  | zero => rfl
  | succ k =>
    have h1 : run0 table 1 (C (k+2) L) = some ⟨3,Z (k+4) ++ true::L,[]⟩ := by rfl
    have h2 := scanD (k+4) (true::L) []
    have h3 : run0 table 6 ⟨3,true::L,O (k+4)⟩ =
        some ⟨2,true::true::true::true::true::L,O k⟩ := by rfl
    have h4 := scanC k (true::true::true::true::L)
    have h5 : run0 table 1 ⟨2,true::(Z k ++ true::true::true::true::L),[]⟩ =
        some (C (k+1) (true::true::true::L)) := by rfl
    have H := join0 (join0 (join0 (join0 h1 (by simpa using h2)) h3) h4) h5
    rw [show 1+(k+4)+6+k+1=2*(k+1)+10 by omega] at H
    exact H

theorem foldC (k : Nat) (L : List Bool) :
    ∃ t, run0 table t (C k L) = some (C 0 (O (3*k) ++ L)) := by
  induction k generalizing L with
  | zero => exact ⟨0,rfl⟩
  | succ k ih =>
    obtain ⟨t,h⟩ := ih (true::true::true::L)
    refine ⟨2*k+10+t,?_⟩
    have H := join0 (stepC k L) h
    have he : O (3*(k+1)) ++ L = O (3*k) ++ true::true::true::L := by
      unfold O
      rw [Nat.mul_succ, ← List.replicate_append_replicate,List.append_assoc]
      rfl
    rw [he]
    exact H

theorem finish_start (L : List Bool) :
    run0 table 9 (C 0 (true::L)) = some ⟨0,true::true::L,[false,true,true]⟩ := by rfl

theorem stepA (L R : List Bool) :
    run0 table 6 ⟨0,true::true::L,false::R⟩ =
       some ⟨0,L,false::true::true::R⟩ := by rfl

theorem foldA (n : Nat) (R : List Bool) :
    run0 table (6*n) ⟨0,O (2*n),false::R⟩ =
       some ⟨0,[],false::(O (2*n) ++ R)⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h1 : run0 table 6 ⟨0,O (2*(n+1)),false::R⟩ =
        some ⟨0,O (2*n),false::true::true::R⟩ := by
      rw [show 2*(n+1)=2*n+2 by omega]
      exact stepA _ _
    have H := join0 h1 (ih (true::true::R))
    rw [show 6+6*n=6*(n+1) by omega] at H
    have he : O (2*(n+1)) ++ R = O (2*n) ++ true::true::R := by
      unfold O
      rw [Nat.mul_succ, ← List.replicate_append_replicate,List.append_assoc]
      rfl
    rw [he]
    exact H

theorem finish (n : Nat) :
    run0 table (9+6*(n+1)) (C 0 (O (2*n+1))) = some (A (2*n+4)) := by
  have h1 : run0 table 9 (C 0 (O (2*n+1))) =
      some ⟨0,O (2*(n+1)),[false,true,true]⟩ := by
    rw [show 2*(n+1)=2*n+2 by omega]
    exact finish_start _
  have H := join0 h1 (foldA (n+1) [true,true])
  have he : O (2*(n+1)) ++ [true,true] = O (2*n+4) := by
    unfold O
    change List.replicate (2*(n+1)) true ++ List.replicate 2 true = _
    rw [List.replicate_append_replicate]
    congr 1
  rw [he] at H
  exact H

theorem epoch (n : Nat) :
    ∃ t, 0 < t ∧ run0 table t (A (2*n+2)) = some (A (2*(3*n+4)+2)) := by
  have h1 := enter (2*n+1)
  obtain ⟨t,h2⟩ := foldC (2*n+2) [true]
  have h2' : run0 table t (C (2*n+2) [true]) = some (C 0 (O (2*(3*n+3)+1))) := by
    have he : 3*(2*n+2)+1=2*(3*n+3)+1 := by omega
    rw [← he]
    simpa only [O,List.replicate_succ'] using h2
  have h3 := finish (3*n+3)
  have H := join0 (join0 h1 h2') h3
  refine ⟨(2+(2*n+1)+1)+t+(9+6*((3*n+3)+1)),by omega,?_⟩
  have he : 2*(3*n+3)+4=2*(3*n+4)+2 := by omega
  simpa only [he] using H

theorem entry : run0 table 17 ⟨0,[],[]⟩ = some (A 4) := by rfl

theorem arbitrary (n : Nat) : ∃ t ≥ n, ∃ z, run0 table t ⟨0,[],[]⟩ = some z := by
  have h : ∀ k : Nat, ∃ t ≥ k, ∃ m, run0 table t ⟨0,[],[]⟩ = some (A (2*m+2)) := by
    intro k
    induction k with
    | zero => exact ⟨17,by omega,1,entry⟩
    | succ k ih =>
      obtain ⟨t,ht,m,hr⟩ := ih
      obtain ⟨u,hu,he⟩ := epoch m
      exact ⟨t+u,by omega,3*m+4,join0 hr he⟩
  obtain ⟨t,ht,m,hr⟩ := h n
  exact ⟨t,ht,A (2*m+2),hr⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table (fun n => by
    obtain ⟨t,ht,z,hr⟩ := arbitrary n
    exact ⟨t,z,ht,hr⟩) m hm

#print axioms arbitrary
#print axioms never
end BB6Coverage.Agent4Raw109RF389
