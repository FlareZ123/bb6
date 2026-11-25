import SweepPumping
import Raw58Live

namespace BB6Coverage.Agent4Raw109LA515
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
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,true,1⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

def O (n : Nat) := List.replicate n true
def F (R : List Bool) : Z0 := ⟨5,[],R⟩
def C (L W : List Bool) : Z0 :=
  ⟨2,W.headD false::L,W.tail⟩

inductive Code : List Bool → Prop where
  | nil : Code []
  | tail : Code [true,false]
  | digit (b : Bool) (W : List Bool) : Code W → Code (false::true::true::b::W)

inductive Sweepable : List Bool → Prop where
  | nil : Sweepable []
  | one (L : List Bool) : Sweepable L → Sweepable (true::L)
  | pair (L : List Bool) : Sweepable L → Sweepable (false::true::L)

theorem addO (n m : Nat) (R : List Bool) :
    O (n+m) ++ R = O n ++ (O m ++ R) := by
  unfold O
  rw [← List.replicate_append_replicate,List.append_assoc]
theorem onesSweepable (n : Nat) : Sweepable (O n) := by
  induction n with
  | zero => exact Sweepable.nil
  | succ n ih => exact Sweepable.one _ ih

theorem sweep (L : List Bool) (h : Sweepable L) (R : List Bool) :
    run0 table L.length ⟨5,L,R⟩ = some (F (L.reverse ++ R)) := by
  induction h generalizing R with
  | nil => rfl
  | one L h ih =>
    have h1 : run0 table 1 ⟨5,true::L,R⟩ = some ⟨5,L,true::R⟩ := by rfl
    have H := join0 h1 (ih (true::R))
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_comm 1 L.length] using H
  | pair L h ih =>
    have h1 : run0 table 2 ⟨5,false::true::L,R⟩ = some ⟨5,L,true::false::R⟩ := by rfl
    have H := join0 h1 (ih (true::false::R))
    have he : (false::true::L).reverse ++ R = L.reverse ++ true::false::R := by
      simp only [List.reverse_cons,List.append_assoc]
      rfl
    rw [he]
    simpa only [List.length_cons,Nat.add_comm 2 L.length,show L.length+1+1=L.length+2 by omega] using H

inductive Acc (n : Nat) : List Bool → List Bool → Prop where
  | base : Acc n (O (2*n+6)) []
  | carry (L P : List Bool) : Acc n L P →
      Acc n (true::true::true::false::L) (P++[false,true,true,true])

theorem accHead (n : Nat) (L P : List Bool) (h : Acc n L P) :
    ∃ T, L = true::T ∧ Sweepable T := by
  induction h with
  | base => exact ⟨O (2*n+5),rfl,onesSweepable _⟩
  | carry L P h ih =>
    obtain ⟨T,rfl,hT⟩ := ih
    exact ⟨_,rfl,Sweepable.one _ (Sweepable.one _ (Sweepable.pair _ hT))⟩

theorem accRev (n : Nat) (L P : List Bool) (h : Acc n L P) :
    L.reverse = O (2*n+6) ++ P := by
  induction h with
  | base => simp [O]
  | carry L P h ih =>
    simp only [List.reverse_cons,ih,List.append_assoc]
    rfl

theorem accCode (n : Nat) (L P : List Bool) (h : Acc n L P) (W : List Bool) (hW : Code W) :
    Code (P++W) := by
  induction h generalizing W with
  | base => exact hW
  | carry L P h ih =>
    rw [List.append_assoc]
    exact ih _ (Code.digit true _ hW)

theorem clearC (T W : List Bool) :
    run0 table 5 (C (true::T) (false::true::true::true::W)) =
      some ⟨5,true::false::true::T,true::false::W⟩ := by rfl
theorem carryC (L W : List Bool) :
    run0 table 4 (C L (false::true::true::false::W)) =
      some (C (true::true::true::false::L) W) := by rfl
theorem emptyC (T : List Bool) :
    run0 table 7 (C (true::T) []) =
      some ⟨5,true::T,[true,false]⟩ := by rfl
theorem tailC (T : List Bool) :
    run0 table 9 (C (true::T) [true,false]) =
      some ⟨5,true::false::true::T,[true,false]⟩ := by rfl

theorem progressC (n : Nat) (W : List Bool) (hW : Code W) (L P : List Bool) (h : Acc n L P) :
    ∃ t V, 0<t ∧ run0 table t (C L W) = some (F (O (2*n+6) ++ V)) ∧ Code V := by
  induction hW generalizing L P with
  | nil =>
    obtain ⟨T,rfl,hT⟩ := accHead n L P h
    have H := join0 (emptyC T) (sweep (true::T) (Sweepable.one _ hT) [true,false])
    rw [accRev n _ P h,List.append_assoc] at H
    exact ⟨_,_,by omega,H,accCode n _ P h _ Code.tail⟩
  | tail =>
    obtain ⟨T,rfl,hT⟩ := accHead n L P h
    have H := join0 (tailC T) (sweep (true::false::true::T) (Sweepable.one _ (Sweepable.pair _ hT)) [true,false])
    have he : (true::false::true::T).reverse ++ [true,false] =
        O (2*n+6) ++ (P ++ [false,true,true,false]) := by
      have hh : (true::false::true::T).reverse = (true::T).reverse ++ [false,true] := by
        simp only [List.reverse_cons,List.append_assoc]
        rfl
      rw [hh]
      rw [accRev n _ P h]
      simp only [List.append_assoc]
      rfl
    rw [he] at H
    exact ⟨_,_,by omega,H,accCode n _ P h _ (Code.digit false _ Code.nil)⟩
  | digit b W hW ih =>
    cases b with
    | false =>
      obtain ⟨t,V,ht,hr,hV⟩ := ih _ _ (Acc.carry _ _ h)
      exact ⟨4+t,V,by omega,join0 (carryC L W) hr,hV⟩
    | true =>
      obtain ⟨T,rfl,hT⟩ := accHead n L P h
      have H := join0 (clearC T W) (sweep (true::false::true::T) (Sweepable.one _ (Sweepable.pair _ hT)) (true::false::W))
      have he : (true::false::true::T).reverse ++ true::false::W =
          O (2*n+6) ++ (P ++ false::true::true::false::W) := by
        have hh : (true::false::true::T).reverse = (true::T).reverse ++ [false,true] := by
          simp only [List.reverse_cons,List.append_assoc]
          rfl
        rw [hh]
        rw [accRev n _ P h]
        simp only [List.append_assoc]
        rfl
      rw [he] at H
      exact ⟨_,_,by omega,H,accCode n _ P h _ (Code.digit false W hW)⟩

theorem pairC (L W : List Bool) :
    run0 table 4 (C L (true::true::W)) = some (C (true::true::L) W) := by rfl
theorem scanC (k : Nat) (L W : List Bool) :
    run0 table (4*k) (C L (O (2*k) ++ W)) = some (C (O (2*k) ++ L) W) := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    have H := join0 (pairC L (O (2*k) ++ W)) (ih (true::true::L))
    rw [show 4+4*k=4*(k+1) by omega] at H
    have he : O (2*(k+1)) ++ L = O (2*k) ++ true::true::L := by
      rw [Nat.mul_succ,addO]
      rfl
    rw [he]
    exact H

theorem progress (n : Nat) (W : List Bool) (hW : Code W) :
    ∃ t V, 0<t ∧ run0 table t (F (O (2*n+4) ++ W)) = some (F (O (2*(n+1)+4) ++ V)) ∧ Code V := by
  have h1 : run0 table 3 (F (O (2*n+4) ++ W)) =
      some (C [true,true] (O (2*n+4) ++ W)) := by rfl
  have h2 := scanC (n+2) [true,true] W
  rw [show 2*(n+2)=2*n+4 by omega] at h2
  have he : O (2*n+4) ++ [true,true] = O (2*n+6) := by
    rw [show 2*n+6=2*n+4+2 by omega]
    change List.replicate (2*n+4) true ++ List.replicate 2 true = _
    exact List.replicate_append_replicate
  rw [he] at h2
  obtain ⟨t,V,ht,hr,hV⟩ := progressC n W hW _ _ (Acc.base)
  have H := join0 (join0 h1 h2) hr
  rw [show 2*n+6=2*(n+1)+4 by omega] at H
  exact ⟨_,V,by omega,H,hV⟩

theorem entry : run0 table 33 ⟨0,[],[]⟩ =
    some (F (O 4 ++ [false,true,true,false])) := by rfl

theorem arbitrary (n : Nat) :
    ∃ t ≥ n, ∃ z, run0 table t ⟨0,[],[]⟩ = some z := by
  have h : ∀ k : Nat, ∃ t ≥ k, ∃ m W, Code W ∧ run0 table t ⟨0,[],[]⟩ = some (F (O (2*m+4) ++ W)) := by
    intro k
    induction k with
    | zero => exact ⟨33,by omega,0,_,Code.digit false _ Code.nil,entry⟩
    | succ k ih =>
      obtain ⟨t,ht,m,W,hW,hr⟩ := ih
      obtain ⟨u,V,hu,hv,hV⟩ := progress m W hW
      exact ⟨t+u,by omega,m+1,V,hV,join0 hr hv⟩
  obtain ⟨t,ht,m,W,_,hr⟩ := h n
  exact ⟨t,ht,F (O (2*m+4) ++ W),hr⟩
#print axioms arbitrary

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table (fun n => by
    obtain ⟨t,ht,z,hr⟩ := arbitrary n
    exact ⟨t,z,ht,hr⟩) m hm
#print axioms never
end BB6Coverage.Agent4Raw109LA515
