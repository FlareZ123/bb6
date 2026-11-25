import BlockPump
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent2Raw124ZeroLF1LE1352
open BB6Coverage BB6Coverage.Agent50Pump BB6Coverage.Agent50Zipper

def table : PartialMachine := fun s =>
  ([some (some ⟨true,true,1⟩),some (some ⟨true,false,1⟩),some (some ⟨true,true,2⟩),none,some (some ⟨false,true,3⟩),some (some ⟨false,false,3⟩),some (some ⟨true,false,3⟩),some (some ⟨true,true,4⟩),some (some ⟨false,true,0⟩),some (some ⟨true,false,5⟩),some (some ⟨true,false,4⟩),some (some ⟨false,false,5⟩)] : List (Option Transition))[2*s.1.val+s.2.toNat]?.getD none
private def words : Nat → List Bool
  | 0 => []
  | n+1 => false::false::true::true::words n
private def stacks : Nat → List Bool
  | 0 => []
  | n+1 => false::true::true::true::stacks n
private def sec (b : Bool) (n : Nat) : HZ := ⟨5,[],if b then true::true::words n else words (n+1)⟩
private def front (l r : List Bool) : HZ := ⟨0,true::false::true::true::l,r⟩
private def back (l r : List Bool) : HZ := ⟨5,true::true::l,r⟩
private theorem enter0 (n : Nat) : hrun table 12 (sec false n) = some (front [false,true] (words n)) := by rfl
private theorem enter1 (n : Nat) : hrun table 12 (sec true n) = some (front [] (words n)) := by rfl
private theorem push (l x : List Bool) : hrun table 10 (front l (false::false::true::true::x)) = some (front (false::true::true::true::l) x) := by rfl
private theorem stackAppend (n : Nat) (l : List Bool) : stacks n ++ false::true::true::true::l = stacks (n+1)++l := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [stacks,List.cons_append,ih]
private theorem scan (n : Nat) (l : List Bool) : hrun table (10*n) (front l (words n)) = some (front (stacks n++l) []) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    have h := hjoin (push l (words n)) (ih (false::true::true::true::l))
    rw [show 10+10*n=10*(n+1) by omega,stackAppend] at h
    exact h
private theorem fill (l : List Bool) : hrun table 12 (front l []) = some (back (false::true::true::true::l) [true,true]) := by rfl
private theorem pop (l x : List Bool) : hrun table 4 (back (false::true::true::true::l) (true::true::x)) = some (back l (true::true::false::false::true::true::x)) := by rfl
private theorem unsweep (n j : Nat) (l : List Bool) : hrun table (4*n) (back (stacks n++l) (true::true::words j)) = some (back l (true::true::words (j+n))) := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    have h := hjoin (pop (stacks n++l) (words j)) (ih (j+1))
    rw [show 4+4*n=4*(n+1) by omega,show j+1+n=j+(n+1) by omega] at h
    exact h
private theorem finish0 (n : Nat) : hrun table 4 (back [false,true] (true::true::words n)) = some (sec true (n+1)) := by rfl
private theorem finish1 (n : Nat) : hrun table 2 (back [] (true::true::words n)) = some (sec false n) := by rfl
private theorem next0 (n : Nat) : ∃ t, 0<t ∧ hrun table t (sec false n) = some (sec true (n+2)) := by
  have h := hjoin (hjoin (enter0 n) (scan n [false,true])) (fill (stacks n++[false,true]))
  have h := hjoin h (unsweep (n+1) 0 [false,true])
  rw [Nat.zero_add] at h
  have h := hjoin h (finish0 (n+1))
  exact ⟨_,by omega,h⟩
private theorem next1 (n : Nat) : ∃ t, 0<t ∧ hrun table t (sec true n) = some (sec false (n+1)) := by
  have h := hjoin (hjoin (enter1 n) (scan n [])) (fill (stacks n++[]))
  have h := hjoin h (unsweep (n+1) 0 [])
  rw [Nat.zero_add] at h
  exact ⟨_,by omega,hjoin h (finish1 (n+1))⟩
private theorem root : hrun table 9 ⟨0,[],[]⟩ = some (sec false 0) := by rfl
private theorem arbitraryLive (n : Nat) : ∃ t b k, n≤t ∧ hrun table t ⟨0,[],[]⟩ = some (sec b k) := by
  induction n with
  | zero => exact ⟨9,false,0,by decide,root⟩
  | succ n ih =>
    obtain ⟨t,b,k,ht,hr⟩ := ih
    cases b with
    | false => obtain ⟨s,hs,hh⟩ := next0 k; exact ⟨t+s,true,k+2,by omega,hjoin hr hh⟩
    | true => obtain ⟨s,hs,hh⟩ := next1 k; exact ⟨t+s,false,k+1,by omega,hjoin hr hh⟩
private theorem blank_eq : embed (HZ.at ⟨0,[],[]⟩ 0) = blank := by
  unfold embed HZ.at blank
  congr 1
  funext x
  simp [atCell]
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨k,b,j,hk,Hk⟩ := arbitraryLive n
  obtain ⟨h',H'⟩ := hrun_sound table k _ _ 0 Hk
  have H := zrun_sound table m hm k _ _ H'
  rw [blank_eq] at H
  rw [show k=n+(k-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some z => rfl
#print axioms never
end BB6.Agent2Raw124ZeroLF1LE1352
