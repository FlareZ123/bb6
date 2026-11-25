import SweepPumping
import Raw58Live

namespace BB6Coverage.Agent4Raw109RF3
open Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,true,1⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none

def O (n : Nat) := List.replicate n true

inductive Code : List Bool → Prop where
  | z2 : Code [false,false]
  | z3 : Code [false,false,false]
  | o3 : Code [true,false,false]
  | z4 : Code [false,false,false,false]
  | o4 : Code [true,false,false,false]
  | s4 : Code [false,true,false,false]
  | b4 : Code [true,true,false,false]
  | digit (b : Bool) (w : List Bool) : Code w → Code (b::true::true::w)

theorem onesCode (n : Nat) : Code (O n ++ [false,false]) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => exact Code.z2
    | 1 => exact Code.o3
    | 2 => exact Code.b4
    | n+3 => exact Code.digit true _ (ih n (by omega))

theorem prefixCode (k : Nat) (w : List Bool) (hw : Code w) :
    Code (O (3*k) ++ w) := by
  induction k with
  | zero => exact hw
  | succ k ih => exact Code.digit true _ ih

def CW (w : List Bool) : Z0 := ⟨2,[false],O 4 ++ w⟩
def F (n : Nat) : Z0 := ⟨5,false::(O (n+6) ++ [false]),[]⟩
def A (k : Nat) (w : List Bool) : Z0 :=
  ⟨0,w.headD false::(O (3*k+4) ++ [false]),w.tail⟩

inductive Safe : Z0 → Prop where
  | c (w : List Bool) : Code w → Safe (CW w)
  | f (n : Nat) : Safe (F n)

theorem scanC (n : Nat) (R : List Bool) :
    run0 table n ⟨2,O n ++ [false],R⟩ =
      some ⟨2,[false],O n ++ R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h1 : run0 table 1 ⟨2,O (n+1) ++ [false],R⟩ =
      some ⟨2,O n ++ [false],true::R⟩ := by rfl
    have H := join0 h1 (ih (true::R))
    rw [Nat.add_comm 1 n] at H
    have he : O (n+1) ++ R = O n ++ true::R := by
      simp only [O,List.replicate_succ',List.append_assoc,List.singleton_append]
    rw [he]
    exact H

theorem clear (k : Nat) (R : List Bool) :
    run0 table (1+(3*k+4)) (A k (true::R)) =
      some (CW (O (3*k) ++ false::R)) := by
  have h1 : run0 table 1 (A k (true::R)) =
      some ⟨2,O (3*k+4) ++ [false],false::R⟩ := by rfl
  have H := join0 h1 (scanC (3*k+4) (false::R))
  have he : O (3*k+4) ++ false::R = O 4 ++ (O (3*k) ++ false::R) := by
    unfold O
    rw [← List.append_assoc,List.replicate_append_replicate,Nat.add_comm 4 (3*k)]
  rw [he] at H
  exact H

theorem carry (k : Nat) (w : List Bool) :
    run0 table 3 (A k (false::true::true::w)) = some (A (k+1) w) := by rfl

theorem clearSecond (k : Nat) :
    run0 table (4+(3*k+5)) (A k [false,true,false,false]) =
      some (CW (O (3*k) ++ [true,false,false,false])) := by
  have h1 : run0 table 4 (A k [false,true,false,false]) =
      some ⟨2,O (3*k+5) ++ [false],[false,false,false]⟩ := by rfl
  have H := join0 h1 (scanC (3*k+5) [false,false,false])
  unfold CW
  have he : O (3*k+5) ++ [false,false,false] =
      O 4 ++ (O (3*k) ++ [true,false,false,false]) := by
    have hs : O 4 ++ O (3*k) ++ [true] = O (3*k+5) := by
      unfold O
      change List.replicate 4 true ++ List.replicate (3*k) true ++ List.replicate 1 true = _
      rw [List.replicate_append_replicate,List.replicate_append_replicate]
      congr 1
      omega
    change O (3*k+5) ++ [false,false,false] = O 4 ++ (O (3*k) ++ ([true] ++ [false,false,false]))
    rw [← List.append_assoc (O (3*k)), ← List.append_assoc (O 4), ← List.append_assoc (O 4) (O (3*k)), hs]
  rw [he] at H
  exact H

theorem zero2 (k : Nat) :
    run0 table 8 (A k [false,false]) = some (F (3*k+2)) := by rfl
theorem zero3 (k : Nat) :
    run0 table 8 (A k [false,false,false]) = some (F (3*k+2)) := by rfl
theorem zero4 (k : Nat) :
    run0 table 8 (A k [false,false,false,false]) = some (F (3*k+2)) := by rfl

theorem progressA (w : List Bool) (hw : Code w) (k : Nat) :
    ∃ t z, 0<t ∧ run0 table t (A k w) = some z ∧ Safe z := by
  induction hw generalizing k with
  | z2 => exact ⟨8,_,by omega,zero2 k,Safe.f _⟩
  | z3 => exact ⟨8,_,by omega,zero3 k,Safe.f _⟩
  | z4 => exact ⟨8,_,by omega,zero4 k,Safe.f _⟩
  | o3 => exact ⟨_,_,by omega,clear k _,Safe.c _ (prefixCode k _ Code.z3)⟩
  | o4 => exact ⟨_,_,by omega,clear k _,Safe.c _ (prefixCode k _ Code.z4)⟩
  | b4 => exact ⟨_,_,by omega,clear k _,Safe.c _ (prefixCode k _ Code.s4)⟩
  | s4 => exact ⟨_,_,by omega,clearSecond k,Safe.c _ (prefixCode k _ Code.o4)⟩
  | digit b w hw ih =>
    cases b with
    | false =>
      obtain ⟨t,z,ht,hr,hs⟩ := ih (k+1)
      exact ⟨3+t,z,by omega,join0 (carry k w) hr,hs⟩
    | true => exact ⟨_,_,by omega,clear k _,Safe.c _ (prefixCode k _ (Code.digit false w hw))⟩

theorem fromC (w : List Bool) :
    run0 table 5 (CW w) = some (A 0 w) := by rfl

theorem fromF (n : Nat) :
    run0 table (2+(n+5)) (F n) =
      some (CW (O (n+1) ++ [false,false])) := by
  have h1 : run0 table 2 (F n) =
      some ⟨2,O (n+5) ++ [false],[false,false]⟩ := by rfl
  have H := join0 h1 (scanC (n+5) [false,false])
  unfold CW O at *
  rw [← List.append_assoc, List.replicate_append_replicate]
  have he : 4+(n+1)=n+5 := by omega
  rw [he]
  exact H

theorem progress (z : Z0) (hz : Safe z) :
    ∃ t y, 0<t ∧ run0 table t z = some y ∧ Safe y := by
  cases hz with
  | f n => exact ⟨_,_,by omega,fromF n,Safe.c _ (onesCode (n+1))⟩
  | c w hw =>
    obtain ⟨t,y,ht,hr,hs⟩ := progressA w hw 0
    exact ⟨5+t,y,by omega,join0 (fromC w) hr,hs⟩

theorem entry : run0 table 50 ⟨0,[],[]⟩ = some (F 2) := by rfl
theorem arbitrary (n : Nat) :
    ∃ t ≥ n, ∃ z, run0 table t ⟨0,[],[]⟩ = some z := by
  have h : ∀ k : Nat, ∃ t ≥ k, ∃ z, Safe z ∧ run0 table t ⟨0,[],[]⟩ = some z := by
    intro k
    induction k with
    | zero => exact ⟨50,by omega,F 2,Safe.f 2,entry⟩
    | succ k ih =>
      obtain ⟨t,ht,z,hs,hr⟩ := ih
      obtain ⟨u,y,hu,hy,hsy⟩ := progress z hs
      exact ⟨t+u,by omega,y,hsy,join0 hr hy⟩
  obtain ⟨t,ht,z,_,hr⟩ := h n
  exact ⟨t,ht,z,hr⟩
#print axioms arbitrary
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table (fun n => by
    obtain ⟨t,ht,z,hr⟩ := arbitrary n
    exact ⟨t,z,ht,hr⟩) m hm

#print axioms never
end BB6Coverage.Agent4Raw109RF3
