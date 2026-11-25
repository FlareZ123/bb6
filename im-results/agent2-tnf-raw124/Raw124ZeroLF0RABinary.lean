import BlockPump

set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent2Raw124ZeroLF0RABinary
open BB6Coverage BB6Coverage.Agent50Pump BB6Coverage.Agent50Zipper

def table : PartialMachine := fun s =>
  ([some (some ⟨true,true,1⟩),some (some ⟨false,true,4⟩),some (some ⟨true,true,2⟩),none,some (some ⟨false,true,3⟩),some (some ⟨true,true,0⟩),some (some ⟨true,false,3⟩),some (some ⟨true,true,4⟩),some (some ⟨true,false,1⟩),some (some ⟨true,false,5⟩),some (some ⟨false,true,0⟩),some (some ⟨false,false,5⟩)] : List (Option Transition))[2*s.1.val+s.2.toNat]?.getD none

private def ones (n : Nat) : List Bool := List.replicate n true
private def zeros (n : Nat) : List Bool := List.replicate n false
private def short1 : List Bool := [false,false,true,true]
private def full1 : List Bool := short1 ++ [false]
private inductive Word : List Bool → Prop where
  | nil : Word []
  | zero {x} : Word x → Word (zeros 5++x)
  | one {x} : Word x → Word (full1++x)
  | last1 : Word short1
private theorem head0 {x} (h : Word x) : x.headD false = false := by cases h <;> rfl
private def sec (r : List Bool) : HZ := ⟨5,[false],r⟩
private def start (k : Nat) (r : List Bool) : HZ := ⟨0,false::ones k++[false],r.tail⟩
private def finish (k : Nat) (r : List Bool) : HZ := ⟨5,ones k++[false],r⟩

private theorem sweep (n : Nat) (r : List Bool) :
    hrun table n (finish n r) = some (sec (zeros n++r)) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    have h : hrun table 1 (finish (n+1) r) = some (finish n (false::r)) := by rfl
    have hh := hjoin h (ih (false::r))
    rw [show 1+n=n+1 by omega] at hh
    rw [show zeros (n+1)++r = zeros n++false::r by simp [zeros,List.replicate_succ',List.append_assoc]]
    exact hh
private theorem enter (x : List Bool) (hx : x.headD false=false) :
    hrun table 1 (sec x) = some (start 0 x) := by
  cases x with
  | nil => rfl
  | cons b x =>
    cases b with
    | false => rfl
    | true => contradiction
private theorem step0 (k : Nat) (x : List Bool) :
    hrun table 7 (start k (zeros 5++x)) = some (finish (k+2) (true::true::false::x)) := by rfl
private theorem step1 (k : Nat) (x : List Bool) (hx : x.headD false=false) :
    hrun table 7 (start k (full1++x)) = some (start (k+5) x) := by
  cases x with
  | nil => rfl
  | cons b x => cases b with | false => rfl | true => contradiction
private theorem stepNil (k : Nat) :
    hrun table 7 (start k []) = some (finish (k+2) [true,true]) := by rfl
private theorem stepLast1 (k : Nat) :
    hrun table 7 (start k short1) = some (start (k+5) []) := by rfl
private theorem zappend (k j : Nat) (r : List Bool) :
    zeros (k+j)++r = zeros k++zeros j++r := by
  simp only [zeros,List.replicate_append_replicate]
private theorem terminal {k j t : Nat} {x r y : List Bool}
    (h : hrun table t (start k x) = some (finish (k+j) r))
    (he : zeros j++r = y) (hy : Word y) (ht : 0<t) :
    ∃ n z, 0<n ∧ Word z ∧ hrun table n (start k x) = some (sec (zeros k++z)) := by
  have hh := hjoin h (sweep (k+j) r)
  rw [zappend,List.append_assoc,he] at hh
  exact ⟨t+(k+j),y,by omega,hy,hh⟩
private theorem carry {x : List Bool} (hx : Word x) (k : Nat) :
    ∃ n y, 0<n ∧ Word y ∧ hrun table n (start k x) = some (sec (zeros k++y)) := by
  induction hx generalizing k with
  | nil => exact terminal (stepNil k) rfl .last1 (by decide)
  | @zero x h ih => exact terminal (step0 k x) rfl (.one h) (by decide)
  | @one x h ih =>
    obtain ⟨t,y,ht,hy,hr⟩ := ih (k+5)
    have hh := hjoin (step1 k x (head0 h)) hr
    rw [zappend,List.append_assoc] at hh
    exact ⟨7+t,_,by omega,.zero hy,hh⟩
  | last1 =>
    obtain ⟨t,y,ht,hy,hr⟩ := terminal (stepNil (k+5)) rfl .last1 (by decide)
    have hh := hjoin (stepLast1 k) hr
    rw [zappend,List.append_assoc] at hh
    exact ⟨7+t,_,by omega,.zero hy,hh⟩
private theorem root : hrun table 10 ⟨0,[],[]⟩ = some (start 0 short1) := by rfl
private theorem next {x} (hx : Word x) :
    ∃ n y, 0<n ∧ Word y ∧ hrun table n (sec x) = some (sec y) := by
  obtain ⟨t,y,ht,hy,hr⟩ := carry hx 0
  exact ⟨1+t,y,by omega,hy,hjoin (enter x (head0 hx)) hr⟩
private theorem arbitraryLive (n : Nat) :
    ∃ t x, n≤t ∧ Word x ∧ hrun table t ⟨0,[],[]⟩ = some (sec x) := by
  induction n with
  | zero =>
    obtain ⟨t,x,ht,hx,hr⟩ := carry (Word.last1) 0
    exact ⟨10+t,x,by omega,hx,hjoin root hr⟩
  | succ n ih =>
    obtain ⟨t,x,ht,hx,hr⟩ := ih
    obtain ⟨s,y,hs,hy,hh⟩ := next hx
    exact ⟨t+s,y,by omega,hy,hjoin hr hh⟩
private theorem blank_eq : embed (HZ.at ⟨0,[],[]⟩ 0) = blank := by
  unfold embed HZ.at blank
  congr 1
  funext x
  simp [atCell]

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨k,x,hk,hx,Hk⟩ := arbitraryLive n
  obtain ⟨h',H'⟩ := hrun_sound table k _ _ 0 Hk
  have H := zrun_sound table m hm k _ _ H'
  rw [blank_eq] at H
  rw [show k=n+(k-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some z => rfl

#print axioms never
end BB6.Agent2Raw124ZeroLF0RABinary
