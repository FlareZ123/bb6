import SweepPumping
import Raw58Live

namespace BB6Coverage.Agent4Raw109LA524
open Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def table (alt : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,true,1⟩)
  | 5,false => some (some ⟨false,true,if alt then 3 else 2⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

def O (n : Nat) := List.replicate n true
def a (alt : Bool) : Nat := if alt then 0 else 1
def F (R : List Bool) : Z0 := ⟨5,[false],R⟩
def B (n : Nat) (b : Bool) (R : List Bool) : Z0 :=
  ⟨1,b::(O (n+2) ++ [false]),R⟩
def C (n : Nat) (W : List Bool) : Z0 :=
  ⟨2,W.headD false::(O (n+2) ++ [false]),W.tail⟩

inductive Code : List Bool → Prop where
  | zero : Code [false]
  | one : Code [true,false]
  | digit (b : Bool) (R : List Bool) : Code R → Code (true::true::true::b::R)

inductive Good (alt : Bool) : List Bool → Prop where
  | digit (b : Bool) (R : List Bool) : Code R → Good alt (O (a alt+2) ++ b::R)

theorem prefixCode (k : Nat) (R : List Bool) (h : Code R) :
    Code (O (4*k) ++ R) := by
  induction k with
  | zero => exact h
  | succ k ih => exact Code.digit true _ ih

theorem addO (n m : Nat) (R : List Bool) :
    O (n+m) ++ R = O n ++ (O m ++ R) := by
  unfold O
  rw [← List.replicate_append_replicate, List.append_assoc]

theorem goodOnes (alt : Bool) (k : Nat) (R : List Bool) (h : Code R) :
    Good alt (O (a alt+2+1+4*k) ++ R) := by
  rw [show a alt+2+1+4*k = a alt+2+(4*k+1) by omega,addO]
  exact Good.digit true _ (prefixCode k R h)

theorem goodClear (alt : Bool) (k : Nat) (R : List Bool) (h : Code R) :
    Good alt (O (a alt+4*k+2) ++ false::R) := by
  cases k with
  | zero => exact Good.digit false _ h
  | succ k =>
    rw [show a alt+4*(k+1)+2 = a alt+2+(4*k+1+3) by omega,addO]
    have hh : O (4*k+1+3) ++ false::R = true::(O (4*k) ++ true::true::true::false::R) := by
      rw [show 4*k+1+3 = 4*k+3+1 by omega]
      change true::(O (4*k+3) ++ false::R) = _
      rw [addO]
      rfl
    rw [hh]
    exact Good.digit true _ (prefixCode k _ (Code.digit false R h))

theorem scan (alt : Bool) (n : Nat) (R : List Bool) :
    run0 (table alt) n ⟨5,O n ++ [false],R⟩ = some (F (O n ++ R)) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h1 : run0 (table alt) 1 ⟨5,O (n+1) ++ [false],R⟩ =
      some ⟨5,O n ++ [false],true::R⟩ := by rfl
    have H := join0 h1 (ih (true::R))
    rw [Nat.add_comm 1 n] at H
    have he : O (n+1) ++ R = O n ++ true::R := by
      simp only [O,List.replicate_succ',List.append_assoc,List.singleton_append]
    rw [he]
    exact H

theorem fromF (alt : Bool) (b : Bool) (R : List Bool) :
    run0 (table alt) (a alt+3) (F (O (a alt+2) ++ b::R)) =
      some (B (a alt) b R) := by cases alt <;> rfl

theorem clearB (alt : Bool) (n : Nat) (R : List Bool) :
    run0 (table alt) (2+(n+1)) (B n true R) =
      some (F (O (n+2) ++ false::R)) := by
  have h1 : run0 (table alt) 2 (B n true R) =
      some ⟨5,O (n+1) ++ [false],true::false::R⟩ := by rfl
  have H := join0 h1 (scan alt (n+1) (true::false::R))
  have he : O (n+2) ++ false::R = O (n+1) ++ true::false::R := by
    simp only [O,List.replicate_succ',List.append_assoc,List.singleton_append] <;> rfl
  rw [he]
  exact H

theorem carryB (alt : Bool) (n : Nat) (R : List Bool) :
    run0 (table alt) 1 (B n false R) = some (C (n+1) R) := by rfl
theorem fromC (alt : Bool) (n : Nat) (b : Bool) (R : List Bool) :
    run0 (table alt) 3 (C n (true::true::true::b::R)) = some (B (n+3) b R) := by rfl

theorem overflow0 (alt : Bool) (n : Nat) :
    run0 (table alt) (7+(n+2)) (C n [false]) =
      some (F (O (n+3) ++ [false])) := by
  have h1 : run0 (table alt) 7 (C n [false]) =
      some ⟨5,O (n+2) ++ [false],[true,false]⟩ := by rfl
  have H := join0 h1 (scan alt (n+2) [true,false])
  have he : O (n+3) ++ [false] = O (n+2) ++ [true,false] := by
    simp only [O,List.replicate_succ',List.append_assoc,List.singleton_append] <;> rfl
  rw [he]
  exact H

theorem overflow1 (alt : Bool) (n : Nat) :
    run0 (table alt) (12+(n+5)) (C n [true,false]) =
      some (F (O (n+6) ++ [false])) := by
  have h1 : run0 (table alt) 12 (C n [true,false]) =
      some ⟨5,O (n+5) ++ [false],[true,false]⟩ := by rfl
  have H := join0 h1 (scan alt (n+5) [true,false])
  have he : O (n+6) ++ [false] = O (n+5) ++ [true,false] := by
    simp only [O,List.replicate_succ',List.append_assoc,List.singleton_append] <;> rfl
  rw [he]
  exact H

theorem progressB (alt : Bool) (R : List Bool) (h : Code R) (k : Nat) (b : Bool) :
    ∃ t W, 0<t ∧ run0 (table alt) t (B (a alt+4*k) b R) = some (F W) ∧ Good alt W := by
  induction h generalizing k b with
  | zero =>
    cases b with
    | true => exact ⟨_,_,by omega,clearB alt _ _,goodClear alt k _ Code.zero⟩
    | false =>
      have H := join0 (carryB alt (a alt+4*k) [false]) (overflow0 alt (a alt+4*k+1))
      have he : a alt+4*k+1+3 = a alt+2+1+4*k+1 := by omega
      rw [he,addO] at H
      exact ⟨_,_,by omega,H,goodOnes alt k _ Code.one⟩
  | one =>
    cases b with
    | true => exact ⟨_,_,by omega,clearB alt _ _,goodClear alt k _ Code.one⟩
    | false =>
      have H := join0 (carryB alt (a alt+4*k) [true,false]) (overflow1 alt (a alt+4*k+1))
      rw [show a alt+4*k+1+6 = a alt+2+1+4*(k+1) by omega] at H
      exact ⟨_,_,by omega,H,goodOnes alt (k+1) _ Code.zero⟩
  | digit c R h ih =>
    cases b with
    | true => exact ⟨_,_,by omega,clearB alt _ _,goodClear alt k _ (Code.digit c R h)⟩
    | false =>
      obtain ⟨t,W,ht,hr,hW⟩ := ih (k+1) c
      have H := join0 (carryB alt (a alt+4*k) (true::true::true::c::R)) (fromC alt (a alt+4*k+1) c R)
      rw [show a alt+4*k+1+3 = a alt+4*(k+1) by omega] at H
      exact ⟨1+3+t,W,by omega,join0 H hr,hW⟩

theorem progress (alt : Bool) (R : List Bool) (h : Good alt R) :
    ∃ t W, 0<t ∧ run0 (table alt) t (F R) = some (F W) ∧ Good alt W := by
  cases h with
  | digit b R h =>
    obtain ⟨t,W,ht,hr,hW⟩ := progressB alt R h 0 b
    exact ⟨a alt+3+t,W,by omega,join0 (fromF alt b R) hr,hW⟩

def start (alt : Bool) : List Bool := if alt then [true,true,false,false] else [true,true,true,true,true,false]
theorem startGood (alt : Bool) : Good alt (start alt) := by
  cases alt
  · exact Good.digit true _ Code.one
  · exact Good.digit false _ Code.zero

theorem entry (alt : Bool) :
    run0 (table alt) (if alt then 17 else 27) ⟨0,[],[]⟩ = some (F (start alt)) := by cases alt <;> rfl

theorem arbitrary (alt : Bool) (n : Nat) :
    ∃ t ≥ n, ∃ z, run0 (table alt) t ⟨0,[],[]⟩ = some z := by
  have h : ∀ k : Nat, ∃ t ≥ k, ∃ R, Good alt R ∧ run0 (table alt) t ⟨0,[],[]⟩ = some (F R) := by
    intro k
    induction k with
    | zero => exact ⟨_,Nat.zero_le _,start alt,startGood alt,entry alt⟩
    | succ k ih =>
      obtain ⟨t,ht,R,hR,hr⟩ := ih
      obtain ⟨u,W,hu,hw,hW⟩ := progress alt R hR
      exact ⟨t+u,by omega,W,hW,join0 hr hw⟩
  obtain ⟨t,ht,R,_,hr⟩ := h n
  exact ⟨t,ht,F R,hr⟩
#print axioms arbitrary

theorem never (alt : Bool) (m : Machine) (hm : compatible (table alt) m) : NeverHalts m :=
  Agent4Live.never_of_live (table alt) (fun n => by
    obtain ⟨t,ht,z,hr⟩ := arbitrary alt n
    exact ⟨t,z,ht,hr⟩) m hm
#print axioms never
end BB6Coverage.Agent4Raw109LA524

namespace BB6Coverage.Agent4Raw109LA524a
abbrev table := Agent4Raw109LA524.table false
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Raw109LA524.never false m hm
#print axioms never
end BB6Coverage.Agent4Raw109LA524a

namespace BB6Coverage.Agent4Raw109LA529a
abbrev table := Agent4Raw109LA524.table true
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Raw109LA524.never true m hm
#print axioms never
end BB6Coverage.Agent4Raw109LA529a
