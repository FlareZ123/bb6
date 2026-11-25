import SweepPumping
import Raw58Live

namespace BB6Coverage.Agent4Raw109LF999
open Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,true,1⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

def L (k : Nat) := rep [true,false,false] k ++ [true,true]
def Z (n : Nat) := List.replicate n false
def E (W : List Bool) : Z0 := ⟨4,[true],false::false::W⟩
def D (k : Nat) (W : List Bool) : Z0 :=
  ⟨3,W.headD false::false::L k,W.tail⟩

inductive Code : List Bool → Prop where
  | endWord : Code [true]
  | digit (b : Bool) (W : List Bool) : Code W → Code (b::false::false::W)

theorem prefixCode (k : Nat) (W : List Bool) (h : Code W) :
    Code (Z (3*k)++W) := by
  induction k with
  | zero => exact h
  | succ k ih => exact Code.digit false _ ih

theorem start (W : List Bool) :
    run0 table 3 (E W) = some (D 0 W) := by rfl
theorem carry (k : Nat) (W : List Bool) :
    run0 table 5 (D k (true::false::false::W)) =
      some (D (k+1) W) := by rfl
theorem carryEnd (k : Nat) :
    run0 table 5 (D k [true]) = some (D (k+1) []) := by rfl

theorem sweep (k : Nat) (R : List Bool) :
    run0 table (3*k+2) ⟨5,false::L k,R⟩ =
      some (E (Z (3*k)++R)) := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h1 : run0 table 3 ⟨5,false::L (k+1),R⟩ =
      some ⟨5,false::L k,false::false::false::R⟩ := by rfl
    have H := join0 h1 (ih (false::false::false::R))
    rw [show 3+(3*k+2)=3*(k+1)+2 by omega] at H
    have he : Z (3*(k+1))++R = Z (3*k)++false::false::false::R := by
      simp only [Z,Nat.mul_succ,List.replicate_succ',List.append_assoc,List.singleton_append]
      rfl
    rw [he]
    exact H

theorem clear (k : Nat) (W : List Bool) :
    run0 table (7+(3*k+2)) (D k (false::false::false::W)) =
      some (E (Z (3*k)++true::false::false::W)) := by
  have h1 : run0 table 7 (D k (false::false::false::W)) =
      some ⟨5,false::L k,true::false::false::W⟩ := by
    cases k <;> rfl
  exact join0 h1 (sweep k (true::false::false::W))
theorem clearEnd (k : Nat) :
    run0 table (7+(3*k+2)) (D k []) =
      some (E (Z (3*k)++[true])) := by
  have h1 : run0 table 7 (D k []) =
      some ⟨5,false::L k,[true]⟩ := by cases k <;> rfl
  exact join0 h1 (sweep k [true])

theorem progressD (W : List Bool) (h : Code W) (k : Nat) :
    ∃ t R, 0<t ∧ run0 table t (D k W) = some (E R) ∧ Code R := by
  induction h generalizing k with
  | endWord =>
    exact ⟨_,_,by omega,join0 (carryEnd k) (clearEnd (k+1)),prefixCode (k+1) _ Code.endWord⟩
  | digit b W h ih =>
    cases b with
    | false => exact ⟨_,_,by omega,clear k W,prefixCode k _ (Code.digit true W h)⟩
    | true =>
      obtain ⟨t,R,ht,hr,hR⟩ := ih (k+1)
      exact ⟨5+t,R,by omega,join0 (carry k W) hr,hR⟩

theorem progress (W : List Bool) (h : Code W) :
    ∃ t R, 0<t ∧ run0 table t (E W) = some (E R) ∧ Code R := by
  obtain ⟨t,R,ht,hr,hR⟩ := progressD W h 0
  exact ⟨3+t,R,by omega,join0 (start W) hr,hR⟩

theorem entry : run0 table 12 ⟨0,[],[]⟩ = some (E [true]) := by rfl
theorem arbitrary (n : Nat) :
    ∃ t ≥ n, ∃ z, run0 table t ⟨0,[],[]⟩ = some z := by
  have h : ∀ k : Nat, ∃ t ≥ k, ∃ W, Code W ∧ run0 table t ⟨0,[],[]⟩ = some (E W) := by
    intro k
    induction k with
    | zero => exact ⟨12,by omega,_,Code.endWord,entry⟩
    | succ k ih =>
      obtain ⟨t,ht,W,hW,hr⟩ := ih
      obtain ⟨u,R,hu,hs,hR⟩ := progress W hW
      exact ⟨t+u,by omega,R,hR,join0 hr hs⟩
  obtain ⟨t,ht,W,_,hr⟩ := h n
  exact ⟨t,ht,E W,hr⟩
#print axioms arbitrary
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table (fun n => by
    obtain ⟨t,ht,z,hr⟩ := arbitrary n
    exact ⟨t,z,ht,hr⟩) m hm
#print axioms never
end BB6Coverage.Agent4Raw109LF999
