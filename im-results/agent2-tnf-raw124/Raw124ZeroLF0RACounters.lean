import BlockPump

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BB6.Agent2Raw124ZeroLF0RACounters
open BB6Coverage BB6Coverage.Agent50Pump BB6Coverage.Agent50Zipper

inductive Variant where
  | v177 | v316 | v318 | v349
  deriving DecidableEq

def table (v : Variant) : PartialMachine := fun s =>
  (match v with
  | .v177 => [some (some ⟨true,true,1⟩),some (some ⟨true,true,3⟩),some (some ⟨true,true,2⟩),none,some (some ⟨false,true,3⟩),some (some ⟨false,false,3⟩),some (some ⟨true,false,3⟩),some (some ⟨true,true,4⟩),some (some ⟨true,true,0⟩),some (some ⟨true,false,5⟩),some (some ⟨false,true,0⟩),some (some ⟨false,false,5⟩)]
  | .v316 => [some (some ⟨true,true,1⟩),some (some ⟨true,true,3⟩),some (some ⟨true,true,2⟩),none,some (some ⟨false,true,3⟩),some (some ⟨true,true,0⟩),some (some ⟨true,false,3⟩),some (some ⟨true,true,4⟩),some (some ⟨false,false,2⟩),some (some ⟨true,false,5⟩),some (some ⟨false,true,0⟩),some (some ⟨false,false,5⟩)]
  | .v318 => [some (some ⟨true,true,1⟩),some (some ⟨true,true,3⟩),some (some ⟨true,true,2⟩),none,some (some ⟨false,true,3⟩),some (some ⟨true,true,0⟩),some (some ⟨true,false,3⟩),some (some ⟨true,true,4⟩),some (some ⟨true,true,0⟩),some (some ⟨true,false,5⟩),some (some ⟨false,true,0⟩),some (some ⟨false,false,5⟩)]
  | .v349 => [some (some ⟨true,true,1⟩),none,some (some ⟨true,true,2⟩),some (some ⟨true,true,3⟩),some (some ⟨false,true,3⟩),some (some ⟨true,true,1⟩),some (some ⟨true,false,3⟩),some (some ⟨true,true,4⟩),some (some ⟨true,true,0⟩),some (some ⟨true,false,5⟩),some (some ⟨false,true,0⟩),some (some ⟨false,false,5⟩)]
  : List (Option Transition))[2*s.1.val+s.2.toNat]?.getD none

private def width : Variant → Nat | .v316 => 5 | _ => 6
private def time1 : Variant → Nat | .v177 => 9 | _ => 7
private def time3 : Variant → Nat | .v177 => 8 | .v316 => 7 | _ => 6
private def ones (n : Nat) : List Bool := List.replicate n true
private def zeros (n : Nat) : List Bool := List.replicate n false
private def short1 : List Bool := [false,false,true,true]
private def short2 : List Bool := [false,false,false,false,true]
private def short3 : List Bool := [false,false,true,true,true]
private def full1 (v : Variant) : List Bool := short1 ++ zeros (width v-4)
private def full2 (v : Variant) : List Bool := short2 ++ zeros (width v-5)
private def full3 (v : Variant) : List Bool := short3 ++ zeros (width v-5)
private inductive Word (v : Variant) : List Bool → Prop where
  | nil : Word v []
  | zero {x} : Word v x → Word v (zeros (width v)++x)
  | one {x} : Word v x → Word v (full1 v++x)
  | two {x} : Word v x → Word v (full2 v++x)
  | three {x} : Word v x → Word v (full3 v++x)
  | last1 : Word v short1
  | last2 : Word v short2
  | last3 : Word v short3
private theorem head0 {v x} (h : Word v x) : x.headD false = false := by
  cases h <;> cases v <;> rfl
private def sec (r : List Bool) : HZ := ⟨5,[false],r⟩
private def start (k : Nat) (r : List Bool) : HZ := ⟨0,false::ones k++[false],r.tail⟩
private def finish (k : Nat) (r : List Bool) : HZ := ⟨5,ones k++[false],r⟩

private theorem sweep (v : Variant) (n : Nat) (r : List Bool) :
    hrun (table v) n (finish n r) = some (sec (zeros n++r)) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    have h : hrun (table v) 1 (finish (n+1) r) = some (finish n (false::r)) := by cases v <;> rfl
    have hh := hjoin h (ih (false::r))
    rw [show 1+n=n+1 by omega] at hh
    rw [show zeros (n+1)++r = zeros n++false::r by simp [zeros,List.replicate_succ',List.append_assoc]]
    exact hh
private theorem enter (v : Variant) (x : List Bool) (hx : x.headD false=false) :
    hrun (table v) 1 (sec x) = some (start 0 x) := by
  cases x with
  | nil => cases v <;> rfl
  | cons b x =>
    cases b with
    | false => cases v <;> rfl
    | true => contradiction
private theorem step0 (v : Variant) (k : Nat) (x : List Bool) :
    hrun (table v) 7 (start k (zeros (width v)++x)) =
      some (finish (k+2) (true::true::zeros (width v-4)++x)) := by cases v <;> rfl
private theorem step1 (v : Variant) (k : Nat) (x : List Bool) :
    hrun (table v) (time1 v) (start k (full1 v++x)) =
      some (finish (k+4) (true::zeros (width v-5)++x)) := by cases v <;> rfl
private theorem step2 (v : Variant) (k : Nat) (x : List Bool) :
    hrun (table v) 7 (start k (full2 v++x)) =
      some (finish (k+2) (true::true::true::zeros (width v-5)++x)) := by cases v <;> rfl
private theorem step3 (v : Variant) (k : Nat) (x : List Bool) (hx : x.headD false=false) :
    hrun (table v) (time3 v) (start k (full3 v++x)) = some (start (k+width v) x) := by
  cases x with
  | nil => cases v <;> rfl
  | cons b x =>
    cases b with
    | false => cases v <;> rfl
    | true => contradiction
private theorem stepNil (v : Variant) (k : Nat) :
    hrun (table v) 7 (start k []) = some (finish (k+2) [true,true]) := by cases v <;> rfl
private theorem stepLast1 (v : Variant) (k : Nat) :
    hrun (table v) (time1 v) (start k short1) = some (finish (k+4) [true]) := by cases v <;> rfl
private theorem stepLast2 (v : Variant) (k : Nat) :
    hrun (table v) 7 (start k short2) = some (finish (k+2) [true,true,true]) := by cases v <;> rfl
private theorem stepLast3 (v : Variant) (k : Nat) :
    hrun (table v) (time3 v) (start k short3) = some (start (k+width v) []) := by cases v <;> rfl
private theorem zappend (k j : Nat) (r : List Bool) :
    zeros (k+j)++r = zeros k++zeros j++r := by
  simp only [zeros,List.replicate_append_replicate]
private theorem terminal {v : Variant} {k j t : Nat} {x r y : List Bool}
    (h : hrun (table v) t (start k x) = some (finish (k+j) r))
    (he : zeros j++r = y) (hy : Word v y) (ht : 0<t) :
    ∃ n z, 0<n ∧ Word v z ∧ hrun (table v) n (start k x) = some (sec (zeros k++z)) := by
  have hh := hjoin h (sweep v (k+j) r)
  rw [zappend,List.append_assoc,he] at hh
  exact ⟨t+(k+j),y,by omega,hy,hh⟩
private theorem carry {v : Variant} {x : List Bool} (hx : Word v x) (k : Nat) :
    ∃ n y, 0<n ∧ Word v y ∧ hrun (table v) n (start k x) = some (sec (zeros k++y)) := by
  induction hx generalizing k with
  | nil => exact terminal (stepNil v k) rfl .last1 (by decide)
  | @zero x h ih => exact terminal (step0 v k x) (by cases v <;> rfl) (.one h) (by decide)
  | @one x h ih => exact terminal (step1 v k x) (by cases v <;> rfl) (.two h) (by cases v <;> decide)
  | @two x h ih => exact terminal (step2 v k x) (by cases v <;> rfl) (.three h) (by decide)
  | @three x h ih =>
    obtain ⟨t,y,ht,hy,hr⟩ := ih (k+width v)
    have hh := hjoin (step3 v k x (head0 h)) hr
    rw [zappend,List.append_assoc] at hh
    exact ⟨time3 v+t,_,by omega,.zero hy,hh⟩
  | last1 => exact terminal (stepLast1 v k) rfl .last2 (by cases v <;> decide)
  | last2 => exact terminal (stepLast2 v k) rfl .last3 (by decide)
  | last3 =>
    obtain ⟨t,y,ht,hy,hr⟩ := terminal (stepNil v (k+width v)) rfl .last1 (by decide)
    have hh := hjoin (stepLast3 v k) hr
    rw [zappend,List.append_assoc] at hh
    exact ⟨time3 v+t,_,by omega,.zero hy,hh⟩
private theorem root (v : Variant) : hrun (table v) 10 ⟨0,[],[]⟩ = some (start 0 short1) := by cases v <;> rfl
private theorem next {v x} (hx : Word v x) :
    ∃ n y, 0<n ∧ Word v y ∧ hrun (table v) n (sec x) = some (sec y) := by
  obtain ⟨t,y,ht,hy,hr⟩ := carry hx 0
  exact ⟨1+t,y,by omega,hy,hjoin (enter v x (head0 hx)) hr⟩
private theorem arbitraryLive (v : Variant) (n : Nat) :
    ∃ t x, n≤t ∧ Word v x ∧ hrun (table v) t ⟨0,[],[]⟩ = some (sec x) := by
  induction n with
  | zero =>
    obtain ⟨t,x,ht,hx,hr⟩ := carry (Word.last1 (v:=v)) 0
    exact ⟨10+t,x,by omega,hx,hjoin (root v) hr⟩
  | succ n ih =>
    obtain ⟨t,x,ht,hx,hr⟩ := ih
    obtain ⟨s,y,hs,hy,hh⟩ := next hx
    exact ⟨t+s,y,by omega,hy,hjoin hr hh⟩
private theorem blank_eq : embed (HZ.at ⟨0,[],[]⟩ 0) = blank := by
  unfold embed HZ.at blank
  congr 1
  funext x
  simp [atCell]

theorem never (v : Variant) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  intro n
  obtain ⟨k,x,hk,hx,Hk⟩ := arbitraryLive v n
  obtain ⟨h',H'⟩ := hrun_sound (table v) k _ _ 0 Hk
  have H := zrun_sound (table v) m hm k _ _ H'
  rw [blank_eq] at H
  rw [show k=n+(k-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some z => rfl

theorem never177 : ∀ m, compatible (table .v177) m → NeverHalts m := never .v177
theorem never316 : ∀ m, compatible (table .v316) m → NeverHalts m := never .v316
theorem never318 : ∀ m, compatible (table .v318) m → NeverHalts m := never .v318
theorem never349 : ∀ m, compatible (table .v349) m → NeverHalts m := never .v349
#print axioms never
end BB6.Agent2Raw124ZeroLF0RACounters
