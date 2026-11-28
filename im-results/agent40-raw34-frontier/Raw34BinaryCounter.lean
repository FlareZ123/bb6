import SweepPumping
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent40Raw34BinaryCounter
open BB6Coverage BB6Coverage.Agent31Pump

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
  simpa only [List.nil_append,List.append_assoc] using h

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
  have h12 := join0 h1 h2
  have h123 := join0 h12 h3
  have h1234 := join0 h123 h4
  have hc : 1+(2*n+3+2*(n+1))=4*n+6 := by omega
  simpa only [rep,List.append_assoc,List.nil_append,hc] using h1234

theorem carryBlank (n : Nat) :
    run0 p (4*n+6) (word ([true]++rep [false,true] n)) =
    some (word (rep [false,false] (n+1)++[true])) := by
  have h1 := enterOne (rep [false,true] n)
  have h2 := scanMany n []
  have h3 := lastBlank (rep [true,true] n++[false,true,true])
  have h4 := clearMany (n+1) [true]
  have h12 := join0 h1 h2
  have h123 := join0 h12 h3
  have h1234 := join0 h123 h4
  have hc : 1+(2*n+3+2*(n+1))=4*n+6 := by omega
  simpa only [rep,List.append_assoc,List.nil_append,hc] using h1234

#print axioms first
#print axioms incEmpty
#print axioms incZero
#print axioms scanMany
#print axioms lastZero
#print axioms lastBlank
#print axioms clearMany
#print axioms carryZero
#print axioms carryBlank

end BB6.Agent40Raw34BinaryCounter
