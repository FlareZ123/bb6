import SweepPumping
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent40Raw34BinaryCounter
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-!
The unfinished Raw34 depth-three child:
  1RB---_1RC---_0RD0LC_1LC1RE_1RD---_------

The original blank start reaches state C on cell 2, with cells 0,1
marked and the right word empty, in precisely two steps. The
subsequent C/D/E computation is a unary-head binary odometer on
odd-position digits with 0 separators; E1 is *never queried*.
This file proves the two exact finite-string macro cases for a
trailing zero and a trailing all-ones overflow. The full all-time
invariant is developed below them.
-/

def p : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨false,false,2⟩)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true  => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,3⟩)
  | _,_ => none

def word (r : List Bool) : Z0 := ⟨2,[false,true,true],r⟩

theorem first : run0 p 2 ⟨0,[],[]⟩ = some (word []) := by decide

theorem incEmpty : run0 p 2 (word []) = some (word [true]) := by decide

theorem incZero (R : List Bool) :
    run0 p 2 (word ([false]++R)) = some (word ([true]++R)) := by
  rfl

theorem enterOne (R : List Bool) :
    run0 p 1 (word ([true]++R)) =
    some ⟨3,[true,false,true,true],R⟩ := by
  rfl

theorem scanPair (L R : List Bool) :
    run0 p 2 ⟨3,[true]++L,[false,true]++R⟩ =
    some ⟨3,[true,true,true]++L,R⟩ := by
  rfl

theorem scanMany (n : Nat) (R : List Bool) :
    run0 p (2*n) ⟨3,[true,false,true,true],rep [false,true] n++R⟩ =
    some ⟨3,[true]++rep [true,true] n++[false,true,true],R⟩ := by
  have h := sweepR p 3 [true] [] [false,true] [true,true] 2
    scanPair n [false,true,true] R
  simpa [List.append_assoc] using h

theorem lastZero (L R : List Bool) :
    run0 p 3 ⟨3,[true]++L,[false,false]++R⟩ =
    some ⟨2,[true,true]++L,[true]++R⟩ := by
  rfl

theorem lastBlank (L : List Bool) :
    run0 p 3 ⟨3,[true]++L,[]⟩ =
    some ⟨2,[true,true]++L,[true]⟩ := by
  rfl

theorem clearPair (L R : List Bool) :
    run0 p 2 ⟨2,[true,true]++L,R⟩ =
    some ⟨2,L,[false,false]++R⟩ := by
  rfl

theorem clearMany (n : Nat) (R : List Bool) :
    run0 p (2*n) ⟨2,rep [true,true] n++[false,true,true],R⟩ =
    some (word (rep [false,false] n++R)) := by
  have h := sweepL p 2 [] [] [true,true] [false,false] 2
    clearPair n [false,true,true] R
  simpa only [List.nil_append,List.append_assoc,word] using h

theorem carryZero (n : Nat) (R : List Bool) :
    run0 p (4*n+6)
      (word ([true]++rep [false,true] n++[false,false]++R)) =
    some (word (rep [false,false] (n+1)++[true]++R)) := by
  have h1 := enterOne (rep [false,true] n++[false,false]++R)
  have h2 := scanMany n ([false,false]++R)
  have h3 := lastZero (rep [true,true] n++[false,true,true]) R
  have h4 := clearMany (n+1) ([true]++R)
  have h2' : run0 p (2*n)
      ⟨3,[true,false,true,true],rep [false,true] n++[false,false]++R⟩ =
      some ⟨3,[true]++rep [true,true] n++[false,true,true],
        [false,false]++R⟩ := by
    simpa only [List.append_assoc] using h2
  have h12 := join0 h1 h2'
  have h123 := join0 h12 h3
  have h1234 := join0 h123 h4
  have hc : 1+2*n+3+2*(n+1)=4*n+6 := by omega
  simpa only [rep,List.append_assoc,List.nil_append,hc] using h1234

theorem carryBlank (n : Nat) :
    run0 p (4*n+6) (word ([true]++rep [false,true] n)) =
    some (word (rep [false,false] (n+1)++[true])) := by
  have h1 := enterOne (rep [false,true] n)
  have h2 := scanMany n []
  have h3 := lastBlank (rep [true,true] n++[false,true,true])
  have h4 := clearMany (n+1) [true]
  have h2' : run0 p (2*n)
      ⟨3,[true,false,true,true],rep [false,true] n⟩ =
      some ⟨3,[true]++rep [true,true] n++[false,true,true],[]⟩ := by
    simpa using h2
  have h12 := join0 h1 h2'
  have h123 := join0 h12 h3
  have h1234 := join0 h123 h4
  have hc : 1+2*n+3+2*(n+1)=4*n+6 := by omega
  simpa only [rep,List.append_assoc,List.nil_append,hc] using h1234


/-! ## An exact inductive grammar for finite binary numerals

The final digit is always one; earlier digits are each followed by a
zero separator. This representation has no arbitrary trailing zeros,
so its zipper is stable under our exact run0 implementation.
The zero numeral is the separate word [] entry case.
-/

inductive Digits where
  | last : Digits
  | zero : Digits → Digits
  | one : Digits → Digits
  deriving DecidableEq, Repr

def encode : Digits → List Bool
  | .last => [true]
  | .zero r => [false,false]++encode r
  | .one r => [true,false]++encode r

def padZeros : Nat → Digits → Digits
  | 0, w => w
  | n+1,w => .zero (padZeros n w)

theorem padZeros_encode (n : Nat) (w : Digits) :
    encode (padZeros n w) = rep [false,false] n++encode w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [padZeros,encode,rep,ih,List.append_assoc]

/-- Every positive numeral begins with either (a) a zero bit;
    (b) some positive block of one-bits before a zero bit; or
    (c) a finite all-one numeral. These cases are exhaustive,
    not an assumption inferred from runtime traces. -/
theorem classify (d : Digits) :
    (∃ r : Digits, encode d = [false,false]++encode r) ∨
    (∃ (n : Nat) (r : Digits),
      encode d = [true]++rep [false,true] n++[false,false,false]++encode r) ∨
    (∃ (n : Nat), encode d = [true]++rep [false,true] n) := by
  induction d with
  | last =>
    exact Or.inr (Or.inr ⟨0,rfl⟩)
  | zero r ih =>
    exact Or.inl ⟨r,rfl⟩
  | one r ih =>
    rcases ih with ⟨u,hu⟩ | ⟨n,u,hu⟩ | ⟨n,hu⟩
    · refine Or.inr (Or.inl ⟨0,u,?_⟩)
      simp [encode,hu,rep,List.append_assoc]
    · refine Or.inr (Or.inl ⟨n+1,u,?_⟩)
      simp [encode,hu,rep,List.append_assoc]
    · refine Or.inr (Or.inr ⟨n+1,?_⟩)
      simp [encode,hu,rep,List.append_assoc]

/-- Every well-formed finite binary numeral has a strictly positive
    exact successor macro which does not query any undefined row.
    Case b=0 takes 2 instructions; a carry through k+1 marked digits
    takes 4k+6 instructions. This is the proof's progress invariant. -/
theorem numeral_progress (d : Digits) :
    ∃ (cost : Nat) (next : Digits),
      0 < cost ∧
      run0 p cost (word (encode d)) =
        some (word (encode next)) := by
  rcases classify d with ⟨r,hr⟩ | ⟨n,r,hr⟩ | ⟨n,hr⟩
  · refine ⟨2,Digits.one r,by omega,?_⟩
    simpa [hr,encode,List.append_assoc] using
      (incZero ([false]++encode r))
  · refine ⟨4*n+6,padZeros (n+1) (Digits.one r),by omega,?_⟩
    simpa [hr,padZeros_encode,encode,List.append_assoc] using
      (carryZero n ([false]++encode r))
  · refine ⟨4*n+6,padZeros (n+1) Digits.last,by omega,?_⟩
    simpa [hr,padZeros_encode,encode,List.append_assoc] using
      (carryBlank n)

/-- For every requested bound n, a genuine blank-start trace of
    length at least n reaches a fully specified C-state numeral.
    This is stronger than observing finitely many counter increments. -/
theorem arbitrarily_long (n : Nat) :
    ∃ (t : Nat) (d : Digits), n ≤ t ∧
      run0 p t ⟨0,[],[]⟩ = some (word (encode d)) := by
  induction n with
  | zero =>
    refine ⟨4,Digits.last,by omega,?_⟩
    simpa [encode] using (join0 first incEmpty)
  | succ n ih =>
    obtain ⟨t,d,ht,hr⟩ := ih
    obtain ⟨cost,next,hcost,hstep⟩ := numeral_progress d
    refine ⟨t+cost,next,by omega,?_⟩
    exact join0 hr hstep

/-- The original six-state Raw34 child is nonhalting on the blank tape
    under every completion of A1,B1,E1,F0,F1. In particular, a HALT
    on E1 does not terminate the binary odometer. -/
theorem all_time_never (m : Machine) (hm : compatible p m) :
    NeverHalts m := by
  intro n
  obtain ⟨t,d,ht,hr⟩ := arbitrarily_long n
  have hz : (zrun p t start).map project = some (word (encode d)) :=
    (run_project p t start).trans hr
  cases h : zrun p t start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound p m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms first
#print axioms incEmpty
#print axioms incZero
#print axioms enterOne
#print axioms scanPair
#print axioms scanMany
#print axioms lastZero
#print axioms lastBlank
#print axioms clearPair
#print axioms clearMany
#print axioms carryZero
#print axioms carryBlank
#print axioms padZeros_encode
#print axioms classify
#print axioms numeral_progress
#print axioms arbitrarily_long
#print axioms all_time_never

end BB6.Agent40Raw34BinaryCounter
