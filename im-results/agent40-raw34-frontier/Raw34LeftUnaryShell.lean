import SweepPumping
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent40Raw34LeftUnaryShell
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-!
A four-hole Raw34 unbounded unary-shell family not covered by a
single translated-ray certificate:
  1RB---_1RC---_0RD1LC_1LC1RF_------_1LC1RF

The head first reaches F on a blank cell with left zipper 01011 at t=6.
From a checkpoint whose left zipper is 0 1^(n+1) 011, the machine
sweeps left across the unary run, turns at the unique zero sentinel,
and sweeps back right, adding exactly one unary mark per macro.
The all-time proof is parametric in n, via original source run0 and
sweepL/sweepR, and all A1,B1,E0,E1 completions may contain HALT.
-/

def p : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨true,false,2⟩)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true  => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true  => some (some ⟨true,true,5⟩)
  | _,_ => none

def word (n : Nat) : Z0 :=
  ⟨5,[false,true]++rep [true] n++[false,true,true],[]⟩

theorem first : run0 p 6 ⟨0,[],[]⟩ = some (word 0) := by decide

theorem fToC (n : Nat) :
    run0 p 1 (word n) =
    some ⟨2,[true]++rep [true] n++[false,true,true],[true]⟩ := by
  rfl

theorem cLeftOne (L R : List Bool) :
    run0 p 1 ⟨2,[true]++L,R⟩ =
      some ⟨2,L,[true]++R⟩ := by rfl

theorem cLeftMany (n : Nat) (L R : List Bool) :
    run0 p n ⟨2,rep [true] n++L,R⟩ =
      some ⟨2,L,rep [true] n++R⟩ := by
  have h := sweepL p 2 [] [] [true] [true] 1
    cLeftOne n L R
  simpa only [List.nil_append,Nat.one_mul] using h

theorem turn (R : List Bool) :
    run0 p 2 ⟨2,[false,true,true],[true,true]++R⟩ =
      some ⟨5,[true,true,false,true,true],R⟩ := by rfl

theorem fRightOne (L R : List Bool) :
    run0 p 1 ⟨5,[true]++L,[true]++R⟩ =
      some ⟨5,[true,true]++L,R⟩ := by rfl

theorem fRightMany (n : Nat) (L R : List Bool) :
    run0 p n ⟨5,[true]++L,rep [true] n++R⟩ =
      some ⟨5,[true]++rep [true] n++L,R⟩ := by
  have h := sweepR p 5 [true] [] [true] [true] 1
    fRightOne n L R
  simpa only [List.nil_append,Nat.one_mul,List.append_assoc] using h

theorem fFinish (L : List Bool) :
    run0 p 1 ⟨5,[true]++L,[]⟩ =
      some ⟨5,[false,true]++L,[]⟩ := by rfl

theorem grow (n : Nat) :
    run0 p (2*n+5) (word n) =
      some (word (n+1)) := by
  have h1 := fToC n
  have h2 := cLeftMany (n+1) [false,true,true] [true]
  have h3 := turn (rep [true] n)
  have h4 := fRightMany n [true,false,true,true] []
  have h5 := fFinish (rep [true] n++[true,false,true,true])
  have h2' : run0 p (n+1)
      ⟨2,[true]++rep [true] n++[false,true,true],[true]⟩ =
      some ⟨2,[false,true,true],[true,true]++rep [true] n⟩ := by
    simpa only [rep,List.append_assoc,rep_snoc] using h2
  have H := join0 (join0 (join0 (join0 h1 h2') h3) h4) h5
  have ht : 1+(n+1)+2+n+1=2*n+5 := by omega
  simpa only [word,rep,List.append_assoc,rep_snoc,ht] using H

theorem all_time_never (m : Machine)
    (hm : compatible p m) : NeverHalts m := by
  exact never_of_growth p word 6 (fun n => 2*n+5)
    first (by intro n; omega) grow m hm

theorem cylinder_mass : cylinderMass p = 25^4 := by decide

#print axioms first
#print axioms cLeftMany
#print axioms turn
#print axioms fRightMany
#print axioms grow
#print axioms all_time_never
#print axioms cylinder_mass
end BB6.Agent40Raw34LeftUnaryShell
