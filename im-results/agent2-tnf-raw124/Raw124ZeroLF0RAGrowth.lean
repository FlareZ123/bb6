import BlockPump

set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent2Raw124ZeroLF0RAGrowth
open BB6Coverage BB6Coverage.Agent50Pump BB6Coverage.Agent50Zipper

def table : PartialMachine := fun s =>
  ([some (some ⟨true,true,1⟩),some (some ⟨true,false,2⟩),some (some ⟨true,true,2⟩),some (some ⟨true,true,5⟩),some (some ⟨false,true,3⟩),some (some ⟨true,false,0⟩),some (some ⟨true,false,3⟩),some (some ⟨true,true,4⟩),none,some (some ⟨true,false,5⟩),some (some ⟨false,true,0⟩),some (some ⟨false,false,5⟩)] : List (Option Transition))[2*s.1.val+s.2.toNat]?.getD none

private def blocks : Nat → List Bool
  | 0 => []
  | n+1 => false::true::true::blocks n
private def stack (n : Nat) : List Bool := blocks n ++ [false]
private def data (n : Nat) : List Bool := (blocks n).tail
private def sec (n : Nat) : HZ := ⟨5,[],false::false::false::data (n+1)⟩
private def mid (k n : Nat) : HZ := ⟨5,stack (k+1),data n⟩
private def back (k : Nat) (r : List Bool) : HZ := ⟨5,stack k,false::false::true::true::r⟩

private theorem enter (n : Nat) : hrun table 10 (sec n) = some (mid 1 n) := by cases n <;> rfl
private theorem push (k n : Nat) : hrun table 9 (mid k (n+1)) = some (mid (k+1) n) := by cases n <;> rfl
private theorem forward (k n : Nat) : hrun table (9*n) (mid k n) = some (mid (k+n) 0) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    have h := hjoin (push k n) (ih (k+1))
    rw [show 9+9*n=9*(n+1) by omega,show k+1+n=k+(n+1) by omega] at h
    exact h
private theorem fill (k : Nat) : hrun table 10 (mid k 0) = some (back (k+1) []) := by rfl
private theorem pop (k : Nat) (r : List Bool) : hrun table 23 (back (k+1) r) = some (back k (false::true::true::r)) := by cases k <;> rfl
private theorem backward (k n : Nat) : hrun table (23*k) (back k (blocks n)) = some (back 0 (blocks (n+k))) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    have h := hjoin (pop k (blocks n)) (ih (n+1))
    rw [show 23+23*k=23*(k+1) by omega,show n+1+k=n+(k+1) by omega] at h
    exact h
private theorem finish (n : Nat) : hrun table 11 (back 0 (blocks n)) = some (sec n) := by rfl
private theorem grow (n : Nat) : ∃ t, 0<t ∧ hrun table t (sec n) = some (sec (n+2)) := by
  have h := hjoin (enter n) (forward 1 n)
  have h := hjoin h (fill (1+n))
  have h := hjoin h (backward (1+n+1) 0)
  have h := hjoin h (finish (0+(1+n+1)))
  rw [show 0+(1+n+1)=n+2 by omega] at h
  exact ⟨_,by omega,h⟩
private theorem root : hrun table 20 ⟨0,[],[]⟩ = some (sec 0) := by rfl
private theorem arbitraryLive (n : Nat) : ∃ t k, n≤t ∧ hrun table t ⟨0,[],[]⟩ = some (sec k) := by
  induction n with
  | zero => exact ⟨20,0,by decide,root⟩
  | succ n ih =>
    obtain ⟨t,k,ht,hr⟩ := ih
    obtain ⟨s,hs,hh⟩ := grow k
    exact ⟨t+s,k+2,by omega,hjoin hr hh⟩
private theorem blank_eq : embed (HZ.at ⟨0,[],[]⟩ 0) = blank := by
  unfold embed HZ.at blank
  congr 1
  funext x
  simp [atCell]

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨k,x,hk,Hk⟩ := arbitraryLive n
  obtain ⟨h',H'⟩ := hrun_sound table k _ _ 0 Hk
  have H := zrun_sound table m hm k _ _ H'
  rw [blank_eq] at H
  rw [show k=n+(k-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some z => rfl
#print axioms never
end BB6.Agent2Raw124ZeroLF0RAGrowth
