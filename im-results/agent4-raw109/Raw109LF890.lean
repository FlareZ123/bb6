import SweepPumping
import Raw58Live

namespace BB6Coverage.Agent4Raw109LF890
open Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0
inductive Variant | a | b | c
def table (v : Variant) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => match v with
    | .a => some (some ⟨false,false,0⟩)
    | .b => some (some ⟨false,false,3⟩)
    | .c => none
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => match v with
    | .c => some (some ⟨false,false,0⟩)
    | _ => none
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => match v with
    | .c => some (some ⟨false,false,2⟩)
    | _ => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨true,true,1⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def S : List Bool := [false,true,false]
def O (n : Nat) := List.replicate n true
def Z (n : Nat) := List.replicate n false
def F (R : List Bool) : Z0 := ⟨5,S,false::false::R⟩
def D (k : Nat) (W : List Bool) : Z0 :=
  ⟨3,W.headD false::false::(O (2*k+1)++S),W.tail⟩
inductive Code : List Bool → Prop where
  | endWord : Code [true]
  | digit (b : Bool) (W : List Bool) : Code W → Code (b::false::W)

theorem prefixCode (k : Nat) (W : List Bool) (h : Code W) :
    Code (Z (2*k)++W) := by
  induction k with
  | zero => exact h
  | succ k ih => exact Code.digit false _ ih

theorem start (v : Variant) (W : List Bool) :
    run0 (table v) 3 (F W) = some (D 0 W) := by rfl

def cost (v : Variant) : Nat := match v with | .b => 8 | _ => 6
theorem carry (v : Variant) (k : Nat) (W : List Bool) :
    run0 (table v) (cost v) (D k (true::false::W)) =
      some (D (k+1) W) := by cases v <;> rfl
theorem carryEnd (v : Variant) (k : Nat) :
    run0 (table v) (cost v) (D k [true]) =
      some (D (k+1) []) := by cases v <;> rfl

theorem sweep (v : Variant) (n : Nat) (R : List Bool) :
    run0 (table v) n ⟨5,O n++S,R⟩ =
      some ⟨5,S,Z n++R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h1 : run0 (table v) 1 ⟨5,O (n+1)++S,R⟩ =
      some ⟨5,O n++S,false::R⟩ := by rfl
    have H := join0 h1 (ih (false::R))
    rw [Nat.add_comm 1 n] at H
    have he : Z (n+1)++R = Z n++false::R := by
      simp only [Z,List.replicate_succ',List.append_assoc,List.singleton_append]
    rw [he]
    exact H

theorem clear (v : Variant) (k : Nat) (W : List Bool) :
    run0 (table v) (5+(2*k+2)) (D k (false::false::W)) =
      some (F (Z (2*k)++true::false::W)) := by
  have h1 : run0 (table v) 5 (D k (false::false::W)) =
      some ⟨5,O (2*k+2)++S,true::false::W⟩ := by rfl
  exact join0 h1 (sweep v (2*k+2) (true::false::W))

theorem clearEnd (v : Variant) (k : Nat) :
    run0 (table v) (5+(2*k+2)) (D k []) =
      some (F (Z (2*k)++[true])) := by
  have h1 : run0 (table v) 5 (D k []) =
      some ⟨5,O (2*k+2)++S,[true]⟩ := by rfl
  exact join0 h1 (sweep v (2*k+2) [true])

theorem progressD (v : Variant) (W : List Bool) (h : Code W) (k : Nat) :
    ∃ t R, 0<t ∧ run0 (table v) t (D k W) = some (F R) ∧ Code R := by
  induction h generalizing k with
  | endWord =>
    exact ⟨_,_,by omega,join0 (carryEnd v k) (clearEnd v (k+1)),prefixCode (k+1) _ Code.endWord⟩
  | digit b W h ih =>
    cases b with
    | false => exact ⟨_,_,by omega,clear v k W,prefixCode k _ (Code.digit true W h)⟩
    | true =>
      obtain ⟨t,R,ht,hr,hR⟩ := ih (k+1)
      exact ⟨_,R,by omega,join0 (carry v k W) hr,hR⟩

theorem progress (v : Variant) (W : List Bool) (h : Code W) :
    ∃ t R, 0<t ∧ run0 (table v) t (F W) = some (F R) ∧ Code R := by
  obtain ⟨t,R,ht,hr,hR⟩ := progressD v W h 0
  exact ⟨3+t,R,by omega,join0 (start v W) hr,hR⟩

theorem entry (v : Variant) : run0 (table v) 37 ⟨0,[],[]⟩ =
    some (F [false,false,true]) := by cases v <;> rfl
theorem arbitrary (v : Variant) (n : Nat) :
    ∃ t ≥ n, ∃ z, run0 (table v) t ⟨0,[],[]⟩ = some z := by
  have h : ∀ k : Nat, ∃ t ≥ k, ∃ W, Code W ∧ run0 (table v) t ⟨0,[],[]⟩ = some (F W) := by
    intro k
    induction k with
    | zero => exact ⟨37,by omega,_,Code.digit false _ Code.endWord,entry v⟩
    | succ k ih =>
      obtain ⟨t,ht,W,hW,hr⟩ := ih
      obtain ⟨u,R,hu,hs,hR⟩ := progress v W hW
      exact ⟨t+u,by omega,R,hR,join0 hr hs⟩
  obtain ⟨t,ht,W,_,hr⟩ := h n
  exact ⟨t,ht,F W,hr⟩
#print axioms arbitrary
theorem never (v : Variant) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  Agent4Live.never_of_live (table v) (fun n => by
    obtain ⟨t,ht,z,hr⟩ := arbitrary v n
    exact ⟨t,z,ht,hr⟩) m hm
#print axioms never
end BB6Coverage.Agent4Raw109LF890

namespace BB6Coverage.Agent4Raw109LF890a
abbrev table := Agent4Raw109LF890.table .a
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Raw109LF890.never .a m hm
end BB6Coverage.Agent4Raw109LF890a

namespace BB6Coverage.Agent4Raw109LF891a
abbrev table := Agent4Raw109LF890.table .b
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Raw109LF890.never .b m hm
end BB6Coverage.Agent4Raw109LF891a

namespace BB6Coverage.Agent4Raw109LF892a
abbrev table := Agent4Raw109LF890.table .c
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Raw109LF890.never .c m hm
end BB6Coverage.Agent4Raw109LF892a
