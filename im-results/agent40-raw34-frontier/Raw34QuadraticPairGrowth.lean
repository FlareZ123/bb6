import SweepPumping
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent40Raw34PairQuadratic
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-!
A parametric nonhalting proof for the easier Raw34 pair parent
D1=0LF, F0=0LD.  This first theorem closes the 15,625-completion
depth-five cylinder

  1RB1LA_1RC1RB_0RD---_1LC0LF_------_0LD1LA

with C1,E0,E1 arbitrary (including HALT).

After 9 blank-tape steps the machine is in A on the blank immediately
left of one 1. The checkpoint family has k+1 contiguous ones to the
right. One macro scans right across the block, executes a fixed
nine-step turnaround, scans left across the enlarged block, and
returns to the same checkpoint shape with one extra one. The exact
macro cost is 2k+11, giving checkpoint time n(n+8) for block length n.
-/

def contiguous : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨true,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true  => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,3⟩)
  | 5,true  => some (some ⟨true,false,0⟩)
  | _,_ => none

def contiguousWord (k : Nat) : Z0 :=
  ⟨0,[],rep [true] (k+1)++[false,false,false]⟩

def contiguousCost (k : Nat) : Nat := 2*k+11

theorem contiguousFirst :
    run0 contiguous 9 ⟨0,[],[]⟩ = some (contiguousWord 0) := by
  decide

theorem contiguousAToB (k : Nat) :
    run0 contiguous 1 (contiguousWord k) =
      some ⟨1,[true,true],rep [true] k++[false,false,false]⟩ := by
  simp [contiguousWord,contiguous,run0,step0,move0,rep]

theorem contiguousBRightOne (L R : List Bool) :
    run0 contiguous 1 ⟨1,[true]++L,[true]++R⟩ =
      some ⟨1,[true,true]++L,R⟩ := by
  rfl

theorem contiguousBRightMany (n : Nat) (L R : List Bool) :
    run0 contiguous n ⟨1,[true]++L,rep [true] n++R⟩ =
      some ⟨1,[true]++rep [true] n++L,R⟩ := by
  have h := sweepR contiguous 1 [true] [] [true] [true] 1
    contiguousBRightOne n L R
  simpa only [List.nil_append,Nat.one_mul,List.append_assoc] using h

theorem contiguousTurn (L : List Bool) :
    run0 contiguous 9 ⟨1,[true]++L,[false,false,false]⟩ =
      some ⟨0,L,[true,false,false,false]⟩ := by
  rfl

theorem contiguousALeftOne (L R : List Bool) :
    run0 contiguous 1 ⟨0,[true]++L,R⟩ =
      some ⟨0,L,[true]++R⟩ := by
  rfl

theorem contiguousALeftMany (n : Nat) (L R : List Bool) :
    run0 contiguous n ⟨0,rep [true] n++L,R⟩ =
      some ⟨0,L,rep [true] n++R⟩ := by
  have h := sweepL contiguous 0 [] [] [true] [true] 1
    contiguousALeftOne n L R
  simpa only [List.nil_append,Nat.one_mul,List.append_assoc] using h

theorem contiguousGrowth (k : Nat) :
    run0 contiguous (contiguousCost k) (contiguousWord k) =
      some (contiguousWord (k+1)) := by
  have h0 := contiguousAToB k
  have h1 := contiguousBRightMany k [true] [false,false,false]
  have h1' : run0 contiguous k
      ⟨1,[true,true],rep [true] k++[false,false,false]⟩ =
      some ⟨1,[true]++rep [true] k++[true],[false,false,false]⟩ := by
    simpa only [List.append_assoc] using h1
  have h2 := contiguousTurn (rep [true] k++[true])
  have h3 := contiguousALeftMany (k+1) [] [true,false,false,false]
  have h2' : run0 contiguous 9
      ⟨1,[true]++rep [true] k++[true],[false,false,false]⟩ =
      some ⟨0,rep [true] (k+1),[true,false,false,false]⟩ := by
    simpa [rep,rep_snoc,List.append_assoc] using h2
  have h3' : run0 contiguous (k+1)
      ⟨0,rep [true] (k+1),[true,false,false,false]⟩ =
      some (contiguousWord (k+1)) := by
    simpa [contiguousWord,rep,rep_snoc,List.append_assoc] using h3
  have H := join0 (join0 (join0 h0 h1') h2') h3'
  have ht : 1+k+9+(k+1) = contiguousCost k := by
    unfold contiguousCost
    omega
  simpa only [List.append_assoc,ht] using H

theorem contiguous_never (m : Machine)
    (hm : compatible contiguous m) : NeverHalts m := by
  exact never_of_growth contiguous contiguousWord 9 contiguousCost
    contiguousFirst (by intro k; unfold contiguousCost; omega)
    contiguousGrowth m hm

#print axioms contiguousFirst
#print axioms contiguousBRightMany
#print axioms contiguousTurn
#print axioms contiguousALeftMany
#print axioms contiguousGrowth
#print axioms contiguous_never
end BB6.Agent40Raw34PairQuadratic
