import SweepPumping
import Raw58Live

namespace BB6Coverage.Agent4Raw109RF506
open Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def table (alt : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => if alt then none else some (some ⟨true,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,true,1⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨true,true,if alt then 3 else 0⟩)
  | _,_ => none

def O (n : Nat) := List.replicate n true

theorem leftOne (alt : Bool) (L R : List Bool) :
    run0 (table alt) 3 ⟨5,false::true::true::L,R⟩ =
      some ⟨5,false::true::L,true::R⟩ := by rfl

theorem leftFold (alt : Bool) (n : Nat) (L R : List Bool) :
    run0 (table alt) (3*n) ⟨5,false::true::(O n ++ L),R⟩ =
      some ⟨5,false::true::L,O n ++ R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have H := join0 (leftOne alt (O n ++ L) R) (ih (true::R))
    rw [show 3+3*n=3*(n+1) by omega] at H
    have he : O (n+1) ++ R = O n ++ true::R := by
      simp only [O,List.replicate_succ',List.append_assoc,List.singleton_append]
    rw [he]
    exact H

theorem turn (alt : Bool) (n : Nat) (L : List Bool) :
    run0 (table alt) 7 ⟨5,[false,true,false]++L,O (4*n+3)⟩ =
      some ⟨5,[true,true,true,true,false,true]++L,O (4*n)⟩ := by rfl

theorem rightOne (alt : Bool) (L R : List Bool) :
    run0 (table alt) 4 ⟨5,true::L,[true,true,true,true]++R⟩ =
      some ⟨5,[true,true,true,true,true]++L,R⟩ := by
  cases alt <;> rfl

theorem rightFold (alt : Bool) (n : Nat) (L : List Bool) :
    run0 (table alt) (4*n) ⟨5,true::L,O (4*n)⟩ =
      some ⟨5,true::(O (4*n) ++ L),[]⟩ := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have h1 : run0 (table alt) 4 ⟨5,true::L,O (4*(n+1))⟩ =
        some ⟨5,true::true::true::true::true::L,O (4*n)⟩ := by
      rw [show 4*(n+1)=4*n+4 by omega]
      exact rightOne alt L (O (4*n))
    have H := join0 h1 (ih (true::true::true::true::L))
    rw [show 4+4*n=4*(n+1) by omega] at H
    have he : O (4*(n+1)) ++ L = O (4*n) ++ true::true::true::true::L := by
      unfold O
      rw [Nat.mul_succ, ← List.replicate_append_replicate, List.append_assoc]
      rfl
    rw [he]
    exact H

def F (n : Nat) (L : List Bool) : Z0 := ⟨5,false::(O (4*n+4) ++ false::L),[]⟩
def exitCost (alt : Bool) := if alt then 11 else 9

theorem exit (alt : Bool) (n : Nat) (L : List Bool) :
    run0 (table alt) (exitCost alt) ⟨5,O (4*n+4) ++ false::true::L,[]⟩ =
      some (F (n+1) (true::L)) := by
  cases alt <;> rfl

theorem epoch (alt : Bool) (n : Nat) (L : List Bool) :
    run0 (table alt) (3*(4*n+3)+7+4*n+exitCost alt) (F n L) =
      some (F (n+1) (true::L)) := by
  have h1 : run0 (table alt) (3*(4*n+3)) (F n L) =
      some ⟨5,[false,true,false]++L,O (4*n+3)⟩ := by
    unfold F
    rw [show O (4*n+4) = true::O (4*n+3) by rfl]
    simpa only [List.cons_append,List.nil_append,List.append_nil] using leftFold alt (4*n+3) (false::L) []
  have h2 := turn alt n L
  have h3 : run0 (table alt) (4*n) ⟨5,[true,true,true,true,false,true]++L,O (4*n)⟩ =
      some ⟨5,O (4*n+4) ++ false::true::L,[]⟩ := by
    have H := rightFold alt n (true::true::true::false::true::L)
    have he : true::(O (4*n) ++ true::true::true::false::true::L) =
        O (4*n+4) ++ false::true::L := by
      have hh : O (4*n) ++ [true,true,true] = O (4*n+3) := by
        unfold O
        change List.replicate (4*n) true ++ List.replicate 3 true = _
        rw [List.replicate_append_replicate]
      change true::(O (4*n) ++ ([true,true,true] ++ false::true::L)) = _
      rw [← List.append_assoc]
      rw [hh]
      rfl
    rw [he] at H
    exact H
  exact join0 (join0 (join0 h1 h2) h3) (exit alt n L)

theorem entry (alt : Bool) :
    run0 (table alt) (if alt then 35 else 33) ⟨0,[],[]⟩ =
      some (F 1 [true]) := by cases alt <;> rfl

theorem arbitrary (alt : Bool) (n : Nat) :
    ∃ t ≥ n, ∃ z, run0 (table alt) t ⟨0,[],[]⟩ = some z := by
  have h : ∀ k : Nat, ∃ t ≥ k, ∃ m L, run0 (table alt) t ⟨0,[],[]⟩ = some (F m L) := by
    intro k
    induction k with
    | zero => exact ⟨_,Nat.zero_le _,1,[true],entry alt⟩
    | succ k ih =>
      obtain ⟨t,ht,m,L,hr⟩ := ih
      exact ⟨t+_,by omega,m+1,true::L,join0 hr (epoch alt m L)⟩
  obtain ⟨t,ht,m,L,hr⟩ := h n
  exact ⟨t,ht,F m L,hr⟩
#print axioms arbitrary
theorem never (alt : Bool) (m : Machine) (hm : compatible (table alt) m) : NeverHalts m :=
  Agent4Live.never_of_live (table alt) (fun n => by
    obtain ⟨t,ht,z,hr⟩ := arbitrary alt n
    exact ⟨t,z,ht,hr⟩) m hm

#print axioms never
end BB6Coverage.Agent4Raw109RF506

namespace BB6Coverage.Agent4Raw109RF506a
abbrev table := Agent4Raw109RF506.table false
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Raw109RF506.never false m hm
#print axioms never
end BB6Coverage.Agent4Raw109RF506a

namespace BB6Coverage.Agent4Raw109RF508a
abbrev table := Agent4Raw109RF506.table true
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Raw109RF506.never true m hm
#print axioms never
end BB6Coverage.Agent4Raw109RF508a
