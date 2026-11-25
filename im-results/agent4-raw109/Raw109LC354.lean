import SweepPumping
import Raw58Live

namespace BB6Coverage.Agent4Raw109LC354
open Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def table (alt : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,true,1⟩)
  | 5,false => some (some ⟨false,true,if alt then 3 else 1⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

def O (n : Nat) := List.replicate n true

inductive Code : List Bool → Prop where
  | z1 : Code [false]
  | z2 : Code [false,false]
  | o2 : Code [true,false]
  | z3 : Code [false,false,false]
  | o3 : Code [true,false,false]
  | s3 : Code [false,true,false]
  | b3 : Code [true,true,false]
  | digit (b c : Bool) (w : List Bool) : Code w → Code (b::c::true::w)

theorem onesCode (n : Nat) : Code (O n ++ [false]) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => exact Code.z1
    | 1 => exact Code.o2
    | 2 => exact Code.b3
    | n+3 => exact Code.digit true true _ (ih n (by omega))

theorem prefixCode (k : Nat) (w : List Bool) (hw : Code w) :
    Code (O (3*k) ++ w) := by
  induction k with
  | zero => exact hw
  | succ k ih => exact Code.digit true true _ ih

def FW (b : Bool) (w : List Bool) : Z0 := ⟨5,[false],true::true::b::true::w⟩
def B (n : Nat) (extra : Bool) : Z0 :=
  ⟨1,false::(O (n+5) ++ [false]),if extra then [false] else []⟩
def A (k : Nat) (w : List Bool) : Z0 :=
  ⟨0,w.headD false::(O (3*k+4) ++ [false]),w.tail⟩

inductive Safe : Z0 → Prop where
  | f (b : Bool) (w : List Bool) : Code w → Safe (FW b w)
  | b (n : Nat) (extra : Bool) : Safe (B n extra)

theorem scanF (alt : Bool) (n : Nat) (R : List Bool) :
    run0 (table alt) n ⟨5,O n ++ [false],R⟩ =
      some ⟨5,[false],O n ++ R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h1 : run0 (table alt) 1 ⟨5,O (n+1) ++ [false],R⟩ =
      some ⟨5,O n ++ [false],true::R⟩ := by rfl
    have H := join0 h1 (ih (true::R))
    rw [Nat.add_comm 1 n] at H
    have he : O (n+1) ++ R = O n ++ true::R := by
      simp only [O,List.replicate_succ',List.append_assoc,List.singleton_append]
    rw [← he] at H
    exact H

theorem clear (alt : Bool) (k : Nat) (R : List Bool) :
    run0 (table alt) (1+(3*k+4)) (A k (true::R)) =
      some (FW true (O (3*k) ++ false::R)) := by
  have h1 : run0 (table alt) 1 (A k (true::R)) =
      some ⟨5,O (3*k+4) ++ [false],false::R⟩ := by rfl
  have H := join0 h1 (scanF alt (3*k+4) (false::R))
  have he : O (3*k+4) ++ false::R = O 4 ++ (O (3*k) ++ false::R) := by
    unfold O
    rw [← List.append_assoc,List.replicate_append_replicate,Nat.add_comm 4 (3*k)]
  rw [he] at H
  exact H

theorem clearSecond (alt : Bool) (k : Nat) (R : List Bool) :
    run0 (table alt) (4+(3*k+5)) (A k (false::true::R)) =
      some (FW true (O (3*k) ++ true::false::R)) := by
  have h1 : run0 (table alt) 4 (A k (false::true::R)) =
      some ⟨5,O (3*k+5) ++ [false],false::R⟩ := by rfl
  have H := join0 h1 (scanF alt (3*k+5) (false::R))
  have he : O (3*k+5) ++ false::R =
      O 4 ++ (O (3*k) ++ true::false::R) := by
    have hs : O 4 ++ O (3*k) ++ [true] = O (3*k+5) := by
      unfold O
      change List.replicate 4 true ++ List.replicate (3*k) true ++ List.replicate 1 true = _
      rw [List.replicate_append_replicate,List.replicate_append_replicate]
      congr 1
      omega
    change O (3*k+5) ++ false::R = O 4 ++ (O (3*k) ++ ([true] ++ false::R))
    rw [← List.append_assoc (O (3*k)), ← List.append_assoc (O 4), ← List.append_assoc (O 4) (O (3*k)), hs]
  rw [he] at H
  exact H

theorem carry (alt : Bool) (k : Nat) (w : List Bool) :
    run0 (table alt) 3 (A k (false::false::true::w)) =
      some (A (k+1) w) := by rfl

theorem zero1 (alt : Bool) (k : Nat) :
    run0 (table alt) 1 (A k [false]) = some (B (3*k) false) := by rfl
theorem zero2 (alt : Bool) (k : Nat) :
    run0 (table alt) 1 (A k [false,false]) = some (B (3*k) false) := by rfl
theorem zero3 (alt : Bool) (k : Nat) :
    run0 (table alt) 1 (A k [false,false,false]) = some (B (3*k) true) := by rfl

theorem progressA (alt : Bool) (w : List Bool) (hw : Code w) (k : Nat) :
    ∃ t z, 0<t ∧ run0 (table alt) t (A k w) = some z ∧ Safe z := by
  induction hw generalizing k with
  | z1 => exact ⟨1,_,by omega,zero1 alt k,Safe.b _ _⟩
  | z2 => exact ⟨1,_,by omega,zero2 alt k,Safe.b _ _⟩
  | z3 => exact ⟨1,_,by omega,zero3 alt k,Safe.b _ _⟩
  | o2 => exact ⟨_,_,by omega,clear alt k _,Safe.f true _ (prefixCode k _ Code.z2)⟩
  | o3 => exact ⟨_,_,by omega,clear alt k _,Safe.f true _ (prefixCode k _ Code.z3)⟩
  | b3 => exact ⟨_,_,by omega,clear alt k _,Safe.f true _ (prefixCode k _ Code.s3)⟩
  | s3 => exact ⟨_,_,by omega,clearSecond alt k _,Safe.f true _ (prefixCode k _ Code.o3)⟩
  | digit b c w hw ih =>
    cases b with
    | true => exact ⟨_,_,by omega,clear alt k _,Safe.f true _ (prefixCode k _ (Code.digit false c w hw))⟩
    | false =>
      cases c with
      | true => exact ⟨_,_,by omega,clearSecond alt k _,Safe.f true _ (prefixCode k _ (Code.digit true false w hw))⟩
      | false =>
        obtain ⟨t,z,ht,hr,hs⟩ := ih (k+1)
        exact ⟨3+t,z,by omega,join0 (carry alt k w) hr,hs⟩

theorem fromF_one (alt : Bool) (w : List Bool) :
    run0 (table alt) (if alt then 8 else 10) (FW true w) =
      some (FW false w) := by cases alt <;> rfl
theorem fromF_zero (alt : Bool) (w : List Bool) :
    run0 (table alt) (if alt then 5 else 7) (FW false w) =
      some (A 0 w) := by cases alt <;> rfl

theorem fromB (alt : Bool) (n : Nat) (extra : Bool) :
    run0 (table alt) (9+(n+7)) (B n extra) =
      some (FW true (O (n+3) ++ [false])) := by
  have h1 : run0 (table alt) 9 (B n extra) =
      some ⟨5,O (n+7) ++ [false],[false]⟩ := by
    cases extra <;> rfl
  have H := join0 h1 (scanF alt (n+7) [false])
  have he : O (n+7) ++ [false] = O 4 ++ (O (n+3) ++ [false]) := by
    unfold O
    rw [← List.append_assoc,List.replicate_append_replicate]
    congr 2
    omega
  rw [he] at H
  exact H

theorem progress (alt : Bool) (z : Z0) (hz : Safe z) :
    ∃ t y, 0<t ∧ run0 (table alt) t z = some y ∧ Safe y := by
  cases hz with
  | b n extra => exact ⟨_,_,by omega,fromB alt n extra,Safe.f true _ (onesCode (n+3))⟩
  | f b w hw =>
    cases b with
    | true => exact ⟨_,_,by cases alt <;> decide,fromF_one alt w,Safe.f false w hw⟩
    | false =>
      obtain ⟨t,y,ht,hr,hs⟩ := progressA alt w hw 0
      exact ⟨(if alt then 5 else 7)+t,y,by omega,join0 (fromF_zero alt w) hr,hs⟩

theorem entry (alt : Bool) :
    run0 (table alt) (if alt then 51 else 59) ⟨0,[],[]⟩ =
      some (B 0 false) := by cases alt <;> rfl

theorem arbitrary (alt : Bool) (n : Nat) :
    ∃ t ≥ n, ∃ z, run0 (table alt) t ⟨0,[],[]⟩ = some z := by
  have h : ∀ k : Nat, ∃ t ≥ k, ∃ z, Safe z ∧ run0 (table alt) t ⟨0,[],[]⟩ = some z := by
    intro k
    induction k with
    | zero => exact ⟨_,Nat.zero_le _,B 0 false,Safe.b _ _,entry alt⟩
    | succ k ih =>
      obtain ⟨t,ht,z,hs,hr⟩ := ih
      obtain ⟨u,y,hu,hy,hsy⟩ := progress alt z hs
      exact ⟨t+u,by omega,y,hsy,join0 hr hy⟩
  obtain ⟨t,ht,z,_,hr⟩ := h n
  exact ⟨t,ht,z,hr⟩
#print axioms arbitrary
theorem never (alt : Bool) (m : Machine) (hm : compatible (table alt) m) : NeverHalts m :=
  Agent4Live.never_of_live (table alt) (fun n => by
    obtain ⟨t,ht,z,hr⟩ := arbitrary alt n
    exact ⟨t,z,ht,hr⟩) m hm

#print axioms never
end BB6Coverage.Agent4Raw109LC354

namespace BB6Coverage.Agent4Raw109LC354a
abbrev table := Agent4Raw109LC354.table false
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Raw109LC354.never false m hm
#print axioms never
end BB6Coverage.Agent4Raw109LC354a

namespace BB6Coverage.Agent4Raw109LC356a
abbrev table := Agent4Raw109LC354.table true
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Raw109LC354.never true m hm
#print axioms never
end BB6Coverage.Agent4Raw109LC356a
