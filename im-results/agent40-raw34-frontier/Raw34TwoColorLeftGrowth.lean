import SweepPumping
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent40Raw34TwoColorLeftGrowth
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-!
A genuine unbounded two-colour (one/zero) leftward growth candidate
for the Raw34 four-hole original physical table:
  1RB---_1RC---_0RD1LC_1LC0RF_------_1RD1RF

State F on a blank and an empty right zipper occurs after six moves.
The left zipper then has the parametric form
  0 1^n 0^(n+2) 11
and every positive-cost macro adds one 1 and one 0:
  n -> n+1 in precisely 2n+6 steps.

Every partial transition in the macro is fixed by these eight cells;
four unassigned cells A1, B1, E0, E1 may be arbitrary, even HALT.
The proof explicitly pumps both the left and right sweeps, then uses
the established infinite-tape soundness bridge, not a finite trace
horizon or an informal claim of eventual periodicity.
-/

def p : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨true,false,2⟩)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true  => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | 5,true  => some (some ⟨true,true,5⟩)
  | _,_ => none

def word (n : Nat) : Z0 :=
  ⟨5,[false]++rep [true] n++rep [false] (n+2)++[true,true],[]⟩

theorem first : run0 p 6 ⟨0,[],[]⟩ = some (word 0) := by decide

theorem fToC (n : Nat) :
    run0 p 2 (word n) =
    some ⟨2,rep [true] (n+1)++rep [false] (n+2)++[true,true],[true]⟩ := by
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

theorem turn (L R : List Bool) :
    run0 p 2 ⟨2,[false]++L,[true,true]++R⟩ =
      some ⟨5,[true,false,false]++L,R⟩ := by rfl

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
    run0 p (2*n+6) (word n) =
      some (word (n+1)) := by
  have h0 := fToC n
  have h1 := cLeftMany (n+1)
    (rep [false] (n+2)++[true,true]) [true]
  have h2 := turn (rep [false] (n+1)++[true,true]) (rep [true] n)
  have h3 := fRightMany n
    ([false,false]++rep [false] (n+1)++[true,true]) []
  have h4 := fFinish
    (rep [true] n++[false,false]++rep [false] (n+1)++[true,true])
  have h1' : run0 p (n+1)
      ⟨2,rep [true] (n+1)++rep [false] (n+2)++[true,true],[true]⟩ =
      some ⟨2,[false]++rep [false] (n+1)++[true,true],
        [true,true]++rep [true] n⟩ := by
    simpa [rep,rep_snoc,List.cons_append,List.nil_append,List.append_assoc] using h1
  have h3' : run0 p n
      ⟨5,[true,false,false]++rep [false] (n+1)++[true,true],
        rep [true] n⟩ =
      some ⟨5,[true]++rep [true] n++[false,false]++
        rep [false] (n+1)++[true,true],[]⟩ := by
    simpa only [List.cons_append,List.nil_append,List.append_assoc] using h3
  have H := join0 (join0 (join0 (join0 h0 h1') h2) h3') h4
  have ht : 2+(n+1)+2+n+1=2*n+6 := by omega
  simpa [word,rep,List.cons_append,List.nil_append,List.append_assoc,ht] using H

theorem all_time_never (m : Machine)
    (hm : compatible p m) : NeverHalts m := by
  exact never_of_growth p word 6 (fun n => 2*n+6)
    first (by intro n; omega) grow m hm

#print axioms first
#print axioms cLeftMany
#print axioms fToC
#print axioms fRightMany
#print axioms turn
#print axioms grow
#print axioms all_time_never
end BB6.Agent40Raw34TwoColorLeftGrowth
