import SweepPumping
import Raw58Live

namespace BB6Coverage.Agent4Raw109LA472
open Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def table : PartialMachine := fun s =>
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
  | 5,false => some (some ⟨false,true,4⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def O (n : Nat) := List.replicate n true
def F (empty : Bool) (R : List Bool) : Z0 := ⟨5,if empty then [] else [false],R⟩
def B (k : Nat) (b : Bool) (R : List Bool) : Z0 :=
  ⟨1,b::(O (4*k+1) ++ [false]),R⟩
def C (k : Nat) (W : List Bool) : Z0 :=
  ⟨2,W.headD false::(O (4*k+2) ++ [false]),W.tail⟩
inductive Code : List Bool → Prop where
  | endWord : Code [true,false]
  | digit (b : Bool) (R : List Bool) : Code R → Code (true::true::true::b::R)
inductive Good : List Bool → Prop where
  | digit (b : Bool) (R : List Bool) : Code R → Good (true::b::R)

theorem addO (n m : Nat) (R : List Bool) :
    O (n+m) ++ R = O n ++ (O m ++ R) := by
  unfold O
  rw [← List.replicate_append_replicate,List.append_assoc]
theorem prefixCode (k : Nat) (R : List Bool) (h : Code R) :
    Code (O (4*k) ++ R) := by
  induction k with
  | zero => exact h
  | succ k ih => exact Code.digit true _ ih
theorem goodClear (k : Nat) (R : List Bool) (h : Code R) :
    Good (O (4*k) ++ true::false::R) := by
  cases k with
  | zero => exact Good.digit false _ h
  | succ k =>
    rw [show 4*(k+1)=4*k+2+2 by omega]
    change Good (true::true::(O (4*k+2) ++ true::false::R))
    rw [addO]
    exact Good.digit true _ (prefixCode k _ (Code.digit false R h))

theorem scan (n : Nat) (L R : List Bool) :
    run0 table (2*n) ⟨5,O (2*n) ++ L,R⟩ =
      some ⟨5,L,O (2*n) ++ R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h1 : run0 table 2 ⟨5,O (2*(n+1)) ++ L,R⟩ =
        some ⟨5,O (2*n) ++ L,true::true::R⟩ := by rfl
    have H := join0 h1 (ih (true::true::R))
    rw [show 2+2*n=2*(n+1) by omega] at H
    have he : O (2*(n+1)) ++ R = O (2*n) ++ true::true::R := by
      rw [Nat.mul_succ,addO]
      rfl
    rw [he]
    exact H

theorem fromF (empty b : Bool) (R : List Bool) :
    run0 table 2 (F empty (true::b::R)) = some (B 0 b R) := by cases empty <;> rfl

theorem clearB (k : Nat) (R : List Bool) :
    run0 table (2+2*(2*k)) (B k true R) =
      some (F false (O (4*k) ++ true::false::R)) := by
  have h1 : run0 table 2 (B k true R) =
      some ⟨5,O (4*k) ++ [false],true::false::R⟩ := by rfl
  have h2 := scan (2*k) [false] (true::false::R)
  rw [show 2*(2*k)=4*k by omega] at h2
  have H := join0 h1 h2
  rw [show 2+4*k=2+2*(2*k) by omega] at H
  exact H

theorem carryB (k : Nat) (R : List Bool) :
    run0 table 1 (B k false R) = some (C k R) := by rfl
theorem fromC (k : Nat) (b : Bool) (R : List Bool) :
    run0 table 3 (C k (true::true::true::b::R)) = some (B (k+1) b R) := by rfl

theorem overflow (k : Nat) :
    run0 table (12+2*(2*k+2)+4) (C k [true,false]) =
      some (F true (true::false::(O (4*(k+1)) ++ [true,false]))) := by
  have h1 : run0 table 12 (C k [true,false]) =
      some ⟨5,O (4*k+5) ++ [false],[true,false]⟩ := by rfl
  have h2 := scan (2*k+2) [true,false] [true,false]
  rw [show 2*(2*k+2)=4*(k+1) by omega] at h2
  have h3 : run0 table 4 ⟨5,[true,false],O (4*(k+1)) ++ [true,false]⟩ =
      some (F true (true::false::(O (4*(k+1)) ++ [true,false]))) := by rfl
  have he : O (4*k+5) ++ [false] = O (4*(k+1)) ++ [true,false] := by
    rw [show 4*k+5=4*(k+1)+1 by omega,addO]
    rfl
  rw [he] at h1
  have H := join0 (join0 h1 h2) h3
  rw [show 12+4*(k+1)+4=12+2*(2*k+2)+4 by omega] at H
  exact H

theorem progressB (k : Nat) (b : Bool) (R : List Bool) (h : Code R) :
    ∃ t e W, 0<t ∧ run0 table t (B k b R) = some (F e W) ∧ Good W := by
  induction h generalizing k b with
  | endWord =>
    cases b with
    | true => exact ⟨_,false,_,by omega,clearB k _,goodClear k _ Code.endWord⟩
    | false => exact ⟨_,true,_,by omega,join0 (carryB k _) (overflow k),
        Good.digit false _ (prefixCode (k+1) _ Code.endWord)⟩
  | digit c R h ih =>
    cases b with
    | true => exact ⟨_,false,_,by omega,clearB k _,goodClear k _ (Code.digit c R h)⟩
    | false =>
      obtain ⟨t,e,W,ht,hr,hW⟩ := ih (k+1) c
      exact ⟨1+3+t,e,W,by omega,join0 (join0 (carryB k _) (fromC k c R)) hr,hW⟩

theorem progress (e : Bool) (R : List Bool) (h : Good R) :
    ∃ t e' W, 0<t ∧ run0 table t (F e R) = some (F e' W) ∧ Good W := by
  cases h with
  | digit b R h =>
    obtain ⟨t,e',W,ht,hr,hW⟩ := progressB 0 b R h
    exact ⟨2+t,e',W,by omega,join0 (fromF e b R) hr,hW⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (F false [true,false,true,false]) := by rfl
theorem arbitrary (n : Nat) :
    ∃ t ≥ n, ∃ z, run0 table t ⟨0,[],[]⟩ = some z := by
  have h : ∀ k : Nat, ∃ t ≥ k, ∃ e R, Good R ∧ run0 table t ⟨0,[],[]⟩ = some (F e R) := by
    intro k
    induction k with
    | zero => exact ⟨15,by omega,false,_,Good.digit false _ Code.endWord,entry⟩
    | succ k ih =>
      obtain ⟨t,ht,e,R,hR,hr⟩ := ih
      obtain ⟨u,e',W,hu,hw,hW⟩ := progress e R hR
      exact ⟨t+u,by omega,e',W,hW,join0 hr hw⟩
  obtain ⟨t,ht,e,R,_,hr⟩ := h n
  exact ⟨t,ht,F e R,hr⟩
#print axioms arbitrary

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table (fun n => by
    obtain ⟨t,ht,z,hr⟩ := arbitrary n
    exact ⟨t,z,ht,hr⟩) m hm
#print axioms never
end BB6Coverage.Agent4Raw109LA472
