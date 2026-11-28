import SweepPumping
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent40Raw34BinaryLeftOdometer
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-!
A new source-level all-time nonhalting proof for the four-hole Raw34 child

  1RB---_1RC1LB_0RD0RC_1LC0LF_------_0LB---

Its F/0 checkpoint acts as an ordinary little-endian binary odometer:
the low bit sits immediately left of F, the high bits extend leftward;
all cells to the right of F stay blank. The source theorem proves a
strictly positive successor macro for EVERY finite Boolean digit word,
including arbitrary leading zeros, so no integer-canonicality
assumption is needed. A1,E0,E1,F1 remain arbitrary even HALT.

This file requires original-source Lean acceptance before its theorem
can be advertised as certified.
-/

def p : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true  => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def word (bits : List Bool) : Z0 := ⟨5,false::bits,[false]⟩

theorem first : run0 p 6 ⟨0,[],[]⟩ = some (word [true,true]) := by decide

theorem incZero (R : List Bool) :
    run0 p 6 (word (false::R)) = some (word (true::R)) := by rfl

theorem incEmpty :
    run0 p 6 (word []) = some (word [true]) := by rfl

theorem fToB (R : List Bool) :
    run0 p 1 (word R) = some ⟨1,R,[false,false]⟩ := by rfl

theorem skipOne (L R : List Bool) :
    run0 p 1 ⟨1,[true]++L,R⟩ =
      some ⟨1,L,[true]++R⟩ := by rfl

theorem skipMany (n : Nat) (L R : List Bool) :
    run0 p n ⟨1,rep [true] n++L,R⟩ =
      some ⟨1,L,rep [true] n++R⟩ := by
  have h := sweepL p 1 [] [] [true] [true] 1 skipOne n L R
  simpa only [List.nil_append,Nat.one_mul] using h

theorem findZero (L R : List Bool) :
    run0 p 1 ⟨1,[false]++L,[true]++R⟩ =
      some ⟨2,[true,true]++L,R⟩ := by rfl

theorem findBlank (R : List Bool) :
    run0 p 1 ⟨1,[],[true]++R⟩ =
      some ⟨2,[true,true],R⟩ := by rfl

theorem scanOne (L R : List Bool) :
    run0 p 1 ⟨2,[true]++L,[true]++R⟩ =
      some ⟨2,[true,false]++L,R⟩ := by rfl

theorem scanMany (n : Nat) (L R : List Bool) :
    run0 p n ⟨2,[true]++L,rep [true] n++R⟩ =
      some ⟨2,[true]++rep [false] n++L,R⟩ := by
  have h := sweepR p 2 [true] [] [true] [false] 1 scanOne n L R
  simpa only [List.nil_append,Nat.one_mul,List.append_assoc] using h

theorem scanToAnchor (L R : List Bool) :
    run0 p 1 ⟨2,[true]++L,[false]++R⟩ =
      some ⟨2,[false,false]++L,R⟩ := by rfl

theorem resetAnchor (L : List Bool) :
    run0 p 4 ⟨2,[false]++L,[false]⟩ =
      some (word L) := by rfl

/-- If k+1 low bits are one and the next higher bit is zero, the carry
    changes those k+1 bits to zeros and flips that higher bit in exactly
    2(k+1)+6 primitive steps, independent of the untouched higher tail. -/
theorem carryZero (n : Nat) (R : List Bool) :
    run0 p (2*(n+1)+6)
      (word ([true]++rep [true] n++[false]++R)) =
    some (word (rep [false] (n+1)++[true]++R)) := by
  have h0 := fToB ([true]++rep [true] n++[false]++R)
  have h1 := skipMany (n+1) ([false]++R) [false,false]
  have h2 := findZero R (rep [true] n++[false,false])
  have h3 := scanMany n ([true]++R) [false,false]
  have h4 := scanToAnchor (rep [false] n++[true]++R) [false]
  have h5 := resetAnchor ([false]++rep [false] n++[true]++R)
  have h0' : run0 p 1 (word ([true]++rep [true] n++[false]++R)) =
      some ⟨1,rep [true] (n+1)++([false]++R),[false,false]⟩ := by
    simpa only [rep,List.append_assoc] using h0
  have h2' : run0 p 1
      ⟨1,[false]++R,rep [true] (n+1)++[false,false]⟩ =
      some ⟨2,[true,true]++R,rep [true] n++[false,false]⟩ := by
    simpa only [rep,List.append_assoc] using h2
  have h3' : run0 p n
      ⟨2,[true,true]++R,rep [true] n++[false,false]⟩ =
      some ⟨2,[true]++rep [false] n++[true]++R,[false,false]⟩ := by
    simpa [List.cons_append,List.nil_append,List.append_assoc] using h3
  have h4' : run0 p 1
      ⟨2,[true]++rep [false] n++[true]++R,[false,false]⟩ =
      some ⟨2,[false]++([false]++rep [false] n++[true]++R),[false]⟩ := by
    simpa [List.cons_append,List.nil_append,List.append_assoc] using h4
  have H := join0 (join0 (join0 (join0 (join0 h0' h1) h2') h3') h4') h5
  have ht : 1+(n+1)+1+n+1+4 = 2*(n+1)+6 := by omega
  simpa only [rep,List.append_assoc,ht] using H

/-- All low bits are one: crossing an unrepresented high blank creates
    a new high bit, and clears the previous low bits. -/
theorem carryBlank (n : Nat) :
    run0 p (2*(n+1)+6)
      (word ([true]++rep [true] n)) =
    some (word (rep [false] (n+1)++[true])) := by
  have h0 := fToB ([true]++rep [true] n)
  have h1 := skipMany (n+1) [] [false,false]
  have h2 := findBlank (rep [true] n++[false,false])
  have h3 := scanMany n [true] [false,false]
  have h4 := scanToAnchor (rep [false] n++[true]) [false]
  have h5 := resetAnchor ([false]++rep [false] n++[true])
  have h0' : run0 p 1 (word ([true]++rep [true] n)) =
      some ⟨1,rep [true] (n+1),[false,false]⟩ := by
    simpa only [rep,List.append_assoc] using h0
  have h1' : run0 p (n+1)
      ⟨1,rep [true] (n+1),[false,false]⟩ =
      some ⟨1,[],rep [true] (n+1)++[false,false]⟩ := by
    simpa only [List.append_nil] using h1
  have h2' : run0 p 1 ⟨1,[],rep [true] (n+1)++[false,false]⟩ =
      some ⟨2,[true,true],rep [true] n++[false,false]⟩ := by
    simpa only [rep,List.append_assoc] using h2
  have h3' : run0 p n ⟨2,[true,true],rep [true] n++[false,false]⟩ =
      some ⟨2,[true]++rep [false] n++[true],[false,false]⟩ := by
    simpa [List.cons_append,List.nil_append,List.append_assoc] using h3
  have h4' : run0 p 1 ⟨2,[true]++rep [false] n++[true],[false,false]⟩ =
      some ⟨2,[false]++([false]++rep [false] n++[true]),[false]⟩ := by
    simpa [List.cons_append,List.nil_append,List.append_assoc] using h4
  have H := join0 (join0 (join0 (join0 (join0 h0' h1') h2') h3') h4') h5
  have ht : 1+(n+1)+1+n+1+4 = 2*(n+1)+6 := by omega
  simpa only [rep,List.append_assoc,ht] using H

/-- Every finite bit string is an initial run of one bits followed by
    a zero and an arbitrary tail, or consists entirely of one bits. -/
theorem splitBits (R : List Bool) :
    (∃ (n : Nat) (T : List Bool),
      R = rep [true] n++[false]++T) ∨
    (∃ (n : Nat), R = rep [true] n) := by
  induction R with
  | nil => exact Or.inr ⟨0,rfl⟩
  | cons b R ih =>
    cases b with
    | false => exact Or.inl ⟨0,R,rfl⟩
    | true =>
      rcases ih with ⟨n,T,h⟩ | ⟨n,h⟩
      · refine Or.inl ⟨n+1,T,?_⟩
        simpa [rep,List.cons_append,List.nil_append,List.append_assoc] using
          congrArg (List.cons true) h
      · refine Or.inr ⟨n+1,?_⟩
        simpa [rep,List.cons_append,List.nil_append,List.append_assoc] using
          congrArg (List.cons true) h

/-- This is the crucial infinite-time argument: EVERY finite binary
    word has a strictly positive fully assigned successor macro. -/
theorem wordProgress (R : List Bool) :
    ∃ (cost : Nat) (T : List Bool),
      0 < cost ∧ run0 p cost (word R) = some (word T) := by
  rcases splitBits R with ⟨n,T,h⟩ | ⟨n,h⟩
  · cases n with
    | zero =>
      refine ⟨6,true::T,by omega,?_⟩
      simpa [h,rep,List.append_assoc] using incZero T
    | succ n =>
      refine ⟨2*(n+1)+6,rep [false] (n+1)++[true]++T,by omega,?_⟩
      simpa [h,rep,List.append_assoc] using carryZero n T
  · cases n with
    | zero =>
      refine ⟨6,[true],by omega,?_⟩
      simpa [h,rep] using incEmpty
    | succ n =>
      refine ⟨2*(n+1)+6,rep [false] (n+1)++[true],by omega,?_⟩
      simpa [h,rep,List.append_assoc] using carryBlank n

/-- All finite time thresholds admit a longer genuine blank-start
    run reaching a F-state binary checkpoint. -/
theorem arbitrarilyLong (n : Nat) :
    ∃ (t : Nat) (R : List Bool),
      n ≤ t ∧ run0 p t ⟨0,[],[]⟩ = some (word R) := by
  induction n with
  | zero => exact ⟨6,[true,true],by omega,first⟩
  | succ n ih =>
    obtain ⟨t,R,ht,hr⟩ := ih
    obtain ⟨cost,T,hpos,hmacro⟩ := wordProgress R
    exact ⟨t+cost,T,by omega,join0 hr hmacro⟩

/-- The original infinite-tape machine, not a time-limited simulator,
    never halts from the true blank tape under ANY completion. -/
theorem all_time_never (m : Machine) (hm : compatible p m) :
    NeverHalts m := by
  intro n
  obtain ⟨t,R,ht,hr⟩ := arbitrarilyLong n
  have hz : (zrun p t start).map project = some (word R) :=
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
#print axioms incZero
#print axioms incEmpty
#print axioms skipMany
#print axioms scanMany
#print axioms carryZero
#print axioms carryBlank
#print axioms splitBits
#print axioms wordProgress
#print axioms arbitrarilyLong
#print axioms all_time_never
end BB6.Agent40Raw34BinaryLeftOdometer
