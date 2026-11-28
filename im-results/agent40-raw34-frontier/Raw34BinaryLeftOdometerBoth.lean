import SweepPumping
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent40Raw34BinaryLeftOdometerBoth
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-!
Parameterize the D1 write bit in the leftward binary odometer:
  1RB---_1RC1LB_0RD0RC_1LC{w}LF_------_0LB---
In both cases F0 witnesses a binary little-endian string. The fixed
right-hand sentinel is exactly w; the reset suffix costs 4 primitive
steps for w=0 and 2 for w=1. Every finite word admits a positive-cost
successor, so the genuine original blank run cannot halt in any
completion of the four unassigned table slots.
-/

def p (w : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true  => some (some ⟨w,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def word (w : Bool) (bits : List Bool) : Z0 :=
  ⟨5,false::bits,[w]⟩

def resetCost (w : Bool) : Nat := if w then 2 else 4

theorem first (w : Bool) :
    run0 (p w) 6 ⟨0,[],[]⟩ = some (word w [true,true]) := by
  cases w <;> decide

theorem incZero (w : Bool) (R : List Bool) :
    run0 (p w) (2+resetCost w) (word w (false::R)) =
      some (word w (true::R)) := by
  cases w <;> rfl

theorem incEmpty (w : Bool) :
    run0 (p w) (2+resetCost w) (word w []) =
      some (word w [true]) := by
  cases w <;> rfl

theorem fToB (w : Bool) (R : List Bool) :
    run0 (p w) 1 (word w R) =
      some ⟨1,R,[false,w]⟩ := by rfl

theorem skipOne (w : Bool) (L R : List Bool) :
    run0 (p w) 1 ⟨1,[true]++L,R⟩ =
      some ⟨1,L,[true]++R⟩ := by rfl

theorem skipMany (w : Bool) (n : Nat) (L R : List Bool) :
    run0 (p w) n ⟨1,rep [true] n++L,R⟩ =
      some ⟨1,L,rep [true] n++R⟩ := by
  have h := sweepL (p w) 1 [] [] [true] [true] 1
    (skipOne w) n L R
  simpa only [List.nil_append,Nat.one_mul] using h

theorem findZero (w : Bool) (L R : List Bool) :
    run0 (p w) 1 ⟨1,[false]++L,[true]++R⟩ =
      some ⟨2,[true,true]++L,R⟩ := by rfl

theorem findBlank (w : Bool) (R : List Bool) :
    run0 (p w) 1 ⟨1,[],[true]++R⟩ =
      some ⟨2,[true,true],R⟩ := by rfl

theorem scanOne (w : Bool) (L R : List Bool) :
    run0 (p w) 1 ⟨2,[true]++L,[true]++R⟩ =
      some ⟨2,[true,false]++L,R⟩ := by rfl

theorem scanMany (w : Bool) (n : Nat) (L R : List Bool) :
    run0 (p w) n ⟨2,[true]++L,rep [true] n++R⟩ =
      some ⟨2,[true]++rep [false] n++L,R⟩ := by
  have h := sweepR (p w) 2 [true] [] [true] [false] 1
    (scanOne w) n L R
  simpa only [List.nil_append,Nat.one_mul,List.append_assoc] using h

theorem scanToAnchor (w : Bool) (L R : List Bool) :
    run0 (p w) 1 ⟨2,[true]++L,[false]++R⟩ =
      some ⟨2,[false,false]++L,R⟩ := by rfl

theorem resetAnchor (w : Bool) (L : List Bool) :
    run0 (p w) (resetCost w) ⟨2,[false]++L,[w]⟩ =
      some (word w L) := by
  cases w <;> rfl

theorem carryZero (w : Bool) (n : Nat) (R : List Bool) :
    run0 (p w) (2*(n+1)+2+resetCost w)
      (word w ([true]++rep [true] n++[false]++R)) =
    some (word w (rep [false] (n+1)++[true]++R)) := by
  have h0 := fToB w ([true]++rep [true] n++[false]++R)
  have h1 := skipMany w (n+1) ([false]++R) [false,w]
  have h2 := findZero w R (rep [true] n++[false,w])
  have h3 := scanMany w n ([true]++R) [false,w]
  have h4 := scanToAnchor w (rep [false] n++[true]++R) [w]
  have h5 := resetAnchor w ([false]++rep [false] n++[true]++R)
  have h0' : run0 (p w) 1 (word w ([true]++rep [true] n++[false]++R)) =
      some ⟨1,rep [true] (n+1)++([false]++R),[false,w]⟩ := by
    simpa only [rep,List.append_assoc] using h0
  have h2' : run0 (p w) 1
      ⟨1,[false]++R,rep [true] (n+1)++[false,w]⟩ =
      some ⟨2,[true,true]++R,rep [true] n++[false,w]⟩ := by
    simpa only [rep,List.append_assoc] using h2
  have h3' : run0 (p w) n
      ⟨2,[true,true]++R,rep [true] n++[false,w]⟩ =
      some ⟨2,[true]++rep [false] n++[true]++R,[false,w]⟩ := by
    simpa only [List.append_assoc] using h3
  have h4' : run0 (p w) 1
      ⟨2,[true]++rep [false] n++[true]++R,[false,w]⟩ =
      some ⟨2,[false]++([false]++rep [false] n++[true]++R),[w]⟩ := by
    simpa only [List.append_assoc] using h4
  have H := join0 (join0 (join0 (join0 (join0 h0' h1) h2') h3') h4') h5
  have ht : 1+(n+1)+1+n+1+resetCost w =
      2*(n+1)+2+resetCost w := by omega
  simpa only [rep,List.append_assoc,ht] using H

theorem carryBlank (w : Bool) (n : Nat) :
    run0 (p w) (2*(n+1)+2+resetCost w)
      (word w ([true]++rep [true] n)) =
    some (word w (rep [false] (n+1)++[true])) := by
  have h0 := fToB w ([true]++rep [true] n)
  have h1 := skipMany w (n+1) [] [false,w]
  have h2 := findBlank w (rep [true] n++[false,w])
  have h3 := scanMany w n [true] [false,w]
  have h4 := scanToAnchor w (rep [false] n++[true]) [w]
  have h5 := resetAnchor w ([false]++rep [false] n++[true])
  have h0' : run0 (p w) 1 (word w ([true]++rep [true] n)) =
      some ⟨1,rep [true] (n+1),[false,w]⟩ := by
    simpa only [rep,List.append_assoc] using h0
  have h2' : run0 (p w) 1
      ⟨1,[],rep [true] (n+1)++[false,w]⟩ =
      some ⟨2,[true,true],rep [true] n++[false,w]⟩ := by
    simpa only [rep,List.append_assoc] using h2
  have h3' : run0 (p w) n
      ⟨2,[true,true],rep [true] n++[false,w]⟩ =
      some ⟨2,[true]++rep [false] n++[true],[false,w]⟩ := by
    simpa only [List.append_assoc] using h3
  have h4' : run0 (p w) 1
      ⟨2,[true]++rep [false] n++[true],[false,w]⟩ =
      some ⟨2,[false]++([false]++rep [false] n++[true]),[w]⟩ := by
    simpa only [List.append_assoc] using h4
  have H := join0 (join0 (join0 (join0 (join0 h0' h1) h2') h3') h4') h5
  have ht : 1+(n+1)+1+n+1+resetCost w =
      2*(n+1)+2+resetCost w := by omega
  simpa only [rep,List.append_assoc,ht] using H

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
        simpa only [rep,List.append_assoc] using
          congrArg (List.cons true) h
      · refine Or.inr ⟨n+1,?_⟩
        simpa only [rep,List.append_assoc] using
          congrArg (List.cons true) h

theorem wordProgress (w : Bool) (R : List Bool) :
    ∃ (cost : Nat) (T : List Bool),
      0 < cost ∧ run0 (p w) cost (word w R) =
        some (word w T) := by
  rcases splitBits R with ⟨n,T,h⟩ | ⟨n,h⟩
  · cases n with
    | zero =>
      refine ⟨2+resetCost w,true::T,by omega,?_⟩
      simpa [h,rep,List.append_assoc] using incZero w T
    | succ n =>
      refine ⟨2*(n+1)+2+resetCost w,
        rep [false] (n+1)++[true]++T,by omega,?_⟩
      simpa [h,rep,List.append_assoc] using carryZero w n T
  · cases n with
    | zero =>
      refine ⟨2+resetCost w,[true],by omega,?_⟩
      simpa [h,rep] using incEmpty w
    | succ n =>
      refine ⟨2*(n+1)+2+resetCost w,
        rep [false] (n+1)++[true],by omega,?_⟩
      simpa [h,rep,List.append_assoc] using carryBlank w n

theorem arbitrarilyLong (w : Bool) (n : Nat) :
    ∃ (t : Nat) (R : List Bool),
      n ≤ t ∧ run0 (p w) t ⟨0,[],[]⟩ =
        some (word w R) := by
  induction n with
  | zero => exact ⟨6,[true,true],by omega,first w⟩
  | succ n ih =>
    obtain ⟨t,R,ht,hr⟩ := ih
    obtain ⟨cost,T,hpos,hmacro⟩ := wordProgress w R
    exact ⟨t+cost,T,by omega,join0 hr hmacro⟩

theorem all_time_never (w : Bool) (m : Machine)
    (hm : compatible (p w) m) : NeverHalts m := by
  intro n
  obtain ⟨t,R,ht,hr⟩ := arbitrarilyLong w n
  have hz : (zrun (p w) t start).map project = some (word w R) :=
    (run_project (p w) t start).trans hr
  cases h : zrun (p w) t start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound (p w) m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

theorem cylinder_mass (w : Bool) :
    cylinderMass (p w) = 25^4 := by
  cases w <;> decide

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
#print axioms cylinder_mass
end BB6.Agent40Raw34BinaryLeftOdometerBoth
