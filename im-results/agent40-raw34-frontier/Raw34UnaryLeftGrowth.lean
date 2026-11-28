import SweepPumping
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent40Raw34UnaryLeftGrowth
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-!
Source-level parametric proof of the *unbounded left-growing unary* Raw34
subfamily, with the D1 write bit w in {0,1}:
  1RB---_1RC1LB_0RD1RC_1LC{w}LF_------_0LB---
The blank run reaches state F with two adjacent ones to its left.
For every k>=2, the F checkpoint with k adjacent one bits executes
a positive-length macro, adds another one at the *previously blank*
cell on the left, and returns to F. Neither an empty-tape finite
simulation nor a guessed time horizon is used to prove nonhalting.
A1,E0,E1,F1 remain arbitrary (including HALT).
-/

def p (w : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨true,true,2⟩)
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

theorem fToB (w : Bool) (R : List Bool) :
    run0 (p w) 1 (word w R) =
      some ⟨1,R,[false,w]⟩ := by rfl

theorem skipOne (w : Bool) (L R : List Bool) :
    run0 (p w) 1 ⟨1,[true]++L,R⟩ =
      some ⟨1,L,[true]++R⟩ := by rfl

theorem skipMany (w : Bool) (n : Nat) (L R : List Bool) :
    run0 (p w) n ⟨1,rep [true] n++L,R⟩ =
      some ⟨1,L,rep [true] n++R⟩ := by
  have h := sweepL (p w) 1 [] [] [true] [true] 1 (skipOne w) n L R
  simpa only [List.nil_append,Nat.one_mul] using h

theorem findBlank (w : Bool) (R : List Bool) :
    run0 (p w) 1 ⟨1,[],[true]++R⟩ =
      some ⟨2,[true,true],R⟩ := by rfl

theorem scanOne (w : Bool) (L R : List Bool) :
    run0 (p w) 1 ⟨2,[true]++L,[true]++R⟩ =
      some ⟨2,[true,true]++L,R⟩ := by rfl

theorem scanMany (w : Bool) (n : Nat) (L R : List Bool) :
    run0 (p w) n ⟨2,[true]++L,rep [true] n++R⟩ =
      some ⟨2,[true]++rep [true] n++L,R⟩ := by
  have h := sweepR (p w) 2 [true] [] [true] [true] 1 (scanOne w) n L R
  simpa only [List.nil_append,Nat.one_mul,List.append_assoc] using h

theorem scanToAnchor (w : Bool) (L R : List Bool) :
    run0 (p w) 1 ⟨2,[true]++L,[false]++R⟩ =
      some ⟨2,[false,true]++L,R⟩ := by rfl

theorem resetAnchor (w : Bool) (L : List Bool) :
    run0 (p w) (resetCost w) ⟨2,[false]++L,[w]⟩ =
      some (word w L) := by
  cases w <;> rfl

/-- Pump n+1 adjacent ones to n+2 adjacent ones. There is an
    arbitrarily long left-moving carry, and its duration is exact. -/
theorem carryBlank (w : Bool) (n : Nat) :
    run0 (p w) (2*(n+1)+2+resetCost w)
      (word w ([true]++rep [true] n)) =
    some (word w ([true]++rep [true] n++[true])) := by
  have h0 := fToB w ([true]++rep [true] n)
  have h1 := skipMany w (n+1) [] [false,w]
  have h2 := findBlank w (rep [true] n++[false,w])
  have h3 := scanMany w n [true] [false,w]
  have h4 := scanToAnchor w (rep [true] n++[true]) [w]
  have h5 := resetAnchor w ([true]++rep [true] n++[true])
  have h0' : run0 (p w) 1 (word w ([true]++rep [true] n)) =
      some ⟨1,rep [true] (n+1),[false,w]⟩ := by
    simpa only [rep,List.append_assoc] using h0
  have h1' : run0 (p w) (n+1)
      ⟨1,rep [true] (n+1),[false,w]⟩ =
      some ⟨1,[],rep [true] (n+1)++[false,w]⟩ := by
    simpa only [List.append_nil] using h1
  have h2' : run0 (p w) 1
      ⟨1,[],rep [true] (n+1)++[false,w]⟩ =
      some ⟨2,[true,true],rep [true] n++[false,w]⟩ := by
    simpa only [rep,List.append_assoc] using h2
  have h3' : run0 (p w) n
      ⟨2,[true,true],rep [true] n++[false,w]⟩ =
      some ⟨2,[true]++rep [true] n++[true],[false,w]⟩ := by
    simpa [List.cons_append,List.nil_append,List.append_assoc] using h3
  have h4' : run0 (p w) 1
      ⟨2,[true]++rep [true] n++[true],[false,w]⟩ =
      some ⟨2,[false]++([true]++rep [true] n++[true]),[w]⟩ := by
    simpa [List.cons_append,List.nil_append,List.append_assoc] using h4
  have H := join0 (join0 (join0 (join0 (join0 h0' h1') h2') h3') h4') h5
  have ht : 1+(n+1)+1+n+1+resetCost w =
      2*(n+1)+2+resetCost w := by omega
  simpa only [List.append_assoc,ht] using H

def family (w : Bool) (k : Nat) : Z0 :=
  word w (rep [true] (k+2))

def cost (w : Bool) (k : Nat) : Nat :=
  2*(k+2)+2+resetCost w

theorem familyFirst (w : Bool) :
    run0 (p w) 6 ⟨0,[],[]⟩ = some (family w 0) := by
  simpa [family,rep,List.cons_append,List.nil_append] using first w

theorem familyGrowth (w : Bool) (k : Nat) :
    run0 (p w) (cost w k) (family w k) =
      some (family w (k+1)) := by
  have h := carryBlank w (k+1)
  have hlen : 2*((k+1)+1)+2+resetCost w = cost w k := by
    unfold cost
    omega
  rw [hlen] at h
  have hstart : [true]++rep [true] (k+1) =
      rep [true] (k+2) := by
    simp [rep,List.cons_append]
  have hend : [true]++rep [true] (k+1)++[true] =
      rep [true] ((k+1)+2) := by
    simp [rep,rep_snoc,List.cons_append,List.append_assoc]
  have hnext : rep [true] (k+2)++[true] =
      rep [true] ((k+1)+2) := by
    have hi : (k+1)+2 = (k+2)+1 := by omega
    rw [hi]
    change rep [true] (k+2)++[true] =
      [true]++rep [true] (k+2)
    exact rep_snoc [true] (k+2)
  simpa only [family,hstart,hnext] using h

/-- A fully parametric original infinite-tape all-time theorem:
    both write-0 and write-1 D1 branches, all four other slots free. -/
theorem all_time_never (w : Bool) (m : Machine)
    (hm : compatible (p w) m) : NeverHalts m := by
  exact never_of_growth (p w) (family w) 6 (cost w)
    (familyFirst w) (by intro k; unfold cost; omega)
    (familyGrowth w) m hm

#print axioms first
#print axioms skipMany
#print axioms scanMany
#print axioms carryBlank
#print axioms familyGrowth
#print axioms all_time_never
end BB6.Agent40Raw34UnaryLeftGrowth
