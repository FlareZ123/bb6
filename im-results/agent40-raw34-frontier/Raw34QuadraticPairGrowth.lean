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
    simpa only [List.cons_append,List.nil_append,List.append_assoc] using h1
  have h2 := contiguousTurn (rep [true] k++[true])
  have h3 := contiguousALeftMany (k+1) [] [true,false,false,false]
  have h2' : run0 contiguous 9
      ⟨1,[true]++rep [true] k++[true],[false,false,false]⟩ =
      some ⟨0,rep [true] (k+1),[true,false,false,false]⟩ := by
    simpa [rep,rep_snoc,List.append_assoc] using h2
  have htail : rep [true] (k+1)++[true,false,false,false] =
      rep [true] ((k+1)+1)++[false,false,false] := by
    calc
      rep [true] (k+1)++[true,false,false,false]
          = (rep [true] (k+1)++[true])++[false,false,false] := by
              simp only [List.append_assoc,List.cons_append,List.nil_append]
      _ = ([true]++rep [true] (k+1))++[false,false,false] := by
              rw [rep_snoc [true] (k+1)]
      _ = rep [true] ((k+1)+1)++[false,false,false] := by rfl
  have h3' : run0 contiguous (k+1)
      ⟨0,rep [true] (k+1),[true,false,false,false]⟩ =
      some (contiguousWord (k+1)) := by
    rw [htail] at h3
    simpa only [List.append_nil,contiguousWord] using h3
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

/-!
The companion 15,625-completion cylinder is

  1RB0LF_1RC1RA_0RD---_1LC0LF_------_0LD1LA

again with C1,E0,E1 arbitrary.  Its checkpoints contain k+1 alternating
10 blocks to the right.  A two-step B/A right sweep converts each remaining
01 pair into two ones; the fixed ten-step turnaround returns in A; a two-step
A/F left sweep converts pairs of ones back into 10 blocks.  The family gains
one block at exact cost 4k+13.
-/

def alternating : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨true,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true  => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,3⟩)
  | 5,true  => some (some ⟨true,false,0⟩)
  | _,_ => none

def alternatingWord (k : Nat) : Z0 :=
  ⟨0,[],rep [true,false] (k+1)++[false,false]⟩

def alternatingCost (k : Nat) : Nat := 4*k+13

theorem alternatingFirst :
    run0 alternating 9 ⟨0,[],[]⟩ = some (alternatingWord 0) := by
  decide

theorem alternatingAToB (k : Nat) :
    run0 alternating 1 (alternatingWord k) =
      some ⟨1,[true,true],
        [false]++rep [true,false] k++[false,false]⟩ := by
  simp [alternatingWord,alternating,run0,step0,move0,rep]

theorem alternatingBRightPair (L R : List Bool) :
    run0 alternating 2 ⟨1,[true]++L,[false,true]++R⟩ =
      some ⟨1,[true,true,true]++L,R⟩ := by
  rfl

theorem alternatingBRightMany (n : Nat) (L R : List Bool) :
    run0 alternating (2*n)
      ⟨1,[true]++L,rep [false,true] n++R⟩ =
      some ⟨1,[true]++rep [true,true] n++L,R⟩ := by
  have h := sweepR alternating 1 [true] [] [false,true] [true,true] 2
    alternatingBRightPair n L R
  simpa only [List.nil_append,List.append_assoc] using h

theorem alternatingTurn (L : List Bool) :
    run0 alternating 10 ⟨1,[true]++L,[false,false,false]⟩ =
      some ⟨0,[true]++L,[true,false,false,false]⟩ := by
  rfl

theorem alternatingALeftPair (L R : List Bool) :
    run0 alternating 2 ⟨0,[true,true]++L,R⟩ =
      some ⟨0,L,[true,false]++R⟩ := by
  rfl

theorem alternatingALeftMany (n : Nat) (L R : List Bool) :
    run0 alternating (2*n)
      ⟨0,rep [true,true] n++L,R⟩ =
      some ⟨0,L,rep [true,false] n++R⟩ := by
  have h := sweepL alternating 0 [] [] [true,true] [true,false] 2
    alternatingALeftPair n L R
  simpa only [List.nil_append,List.append_assoc] using h

theorem alternatingGrowth (k : Nat) :
    run0 alternating (alternatingCost k) (alternatingWord k) =
      some (alternatingWord (k+1)) := by
  have h0 := alternatingAToB k
  have hr0 := rotate false [true] k
  have hr : [false]++rep [true,false] k++[false,false] =
      rep [false,true] k++[false,false,false] := by
    have h := congrArg (fun xs => xs++[false,false]) hr0
    simpa only [List.cons_append,List.nil_append,List.append_assoc] using h
  have h1 := alternatingBRightMany k [true] [false,false,false]
  have h0' : run0 alternating 1 (alternatingWord k) =
      some ⟨1,[true,true],rep [false,true] k++[false,false,false]⟩ := by
    rw [hr] at h0
    exact h0
  have h1' : run0 alternating (2*k)
      ⟨1,[true,true],rep [false,true] k++[false,false,false]⟩ =
      some ⟨1,[true]++rep [true,true] k++[true],
        [false,false,false]⟩ := by
    simpa only [List.cons_append,List.nil_append,List.append_assoc] using h1
  have h2 := alternatingTurn (rep [true,true] k++[true])
  have hrot := congrArg (fun xs => xs++[true]) (rotate true [true] k)
  have hone : [true]++rep [true,true] k++[true] =
      rep [true,true] (k+1) := by
    calc
      [true]++rep [true,true] k++[true]
          = rep [true,true] k++[true,true] := by
              simpa only [List.cons_append,List.nil_append,List.append_assoc] using hrot
      _ = [true,true]++rep [true,true] k := rep_snoc [true,true] k
      _ = rep [true,true] (k+1) := by rfl
  have honeR : [true]++(rep [true,true] k++[true]) =
      rep [true,true] (k+1) := by
    rw [← List.append_assoc]
    exact hone
  have h2' : run0 alternating 10
      ⟨1,[true]++rep [true,true] k++[true],[false,false,false]⟩ =
      some ⟨0,rep [true,true] (k+1),[true,false,false,false]⟩ := by
    simpa only [honeR,List.append_assoc] using h2
  have h3 := alternatingALeftMany (k+1) [] [true,false,false,false]
  have htail : rep [true,false] (k+1)++[true,false,false,false] =
      rep [true,false] ((k+1)+1)++[false,false] := by
    calc
      rep [true,false] (k+1)++[true,false,false,false]
          = (rep [true,false] (k+1)++[true,false])++[false,false] := by
              simp only [List.append_assoc,List.cons_append,List.nil_append]
      _ = ([true,false]++rep [true,false] (k+1))++[false,false] := by
              rw [rep_snoc [true,false] (k+1)]
      _ = rep [true,false] ((k+1)+1)++[false,false] := by rfl
  have h3' : run0 alternating (2*(k+1))
      ⟨0,rep [true,true] (k+1),[true,false,false,false]⟩ =
      some (alternatingWord (k+1)) := by
    rw [htail] at h3
    simpa only [List.append_nil,alternatingWord] using h3
  have H := join0 (join0 (join0 h0' h1') h2') h3'
  have ht : 1+2*k+10+2*(k+1) = alternatingCost k := by
    unfold alternatingCost
    omega
  simpa only [List.append_assoc,ht] using H

theorem alternating_never (m : Machine)
    (hm : compatible alternating m) : NeverHalts m := by
  exact never_of_growth alternating alternatingWord 9 alternatingCost
    alternatingFirst (by intro k; unfold alternatingCost; omega)
    alternatingGrowth m hm

#print axioms alternatingFirst
#print axioms alternatingBRightMany
#print axioms alternatingTurn
#print axioms alternatingALeftMany
#print axioms alternatingGrowth
#print axioms alternating_never

/-! A third easy-pair residual has a stationary-head unary pump.
The cylinder
  1RB1RA_1RC---_0RD---_1LC0LF_1RA1LE_0LD0LE
leaves B1 and C1 arbitrary.  Checkpoints occur with k+1 contiguous ones
immediately left of A; the next checkpoint costs 2k+12. -/

def stationary : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨true,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true  => some (some ⟨false,false,5⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true  => some (some ⟨true,false,4⟩)
  | 5,false => some (some ⟨false,false,3⟩)
  | 5,true  => some (some ⟨false,false,4⟩)
  | _,_ => none

def stationaryWord (k : Nat) : Z0 :=
  ⟨0,[false]++rep [true] (k+1),[false,false,false]⟩

def stationaryCost (k : Nat) : Nat := 2*k+12

theorem stationaryFirst :
    run0 stationary 10 ⟨0,[],[]⟩ = some (stationaryWord 0) := by
  decide

theorem stationaryTurn (L : List Bool) :
    run0 stationary 9 ⟨0,[false]++L,[false,false,false]⟩ =
      some ⟨4,L,[false,false,false,false]⟩ := by
  rfl

theorem stationaryELeftOne (L R : List Bool) :
    run0 stationary 1 ⟨4,[true]++L,R⟩ =
      some ⟨4,L,[true]++R⟩ := by
  rfl

theorem stationaryELeftMany (n : Nat) (L R : List Bool) :
    run0 stationary n ⟨4,rep [true] n++L,R⟩ =
      some ⟨4,L,rep [true] n++R⟩ := by
  have h := sweepL stationary 4 [] [] [true] [true] 1
    stationaryELeftOne n L R
  simpa only [List.nil_append,Nat.one_mul,List.append_assoc] using h

theorem stationaryEToA (k : Nat) :
    run0 stationary 1
      ⟨4,[],rep [true] (k+1)++[false,false,false,false]⟩ =
      some ⟨0,[true,true],rep [true] k++[false,false,false,false]⟩ := by
  change run0 stationary 1
      ⟨4,[],[true]++rep [true] k++[false,false,false,false]⟩ =
      some ⟨0,[true,true],rep [true] k++[false,false,false,false]⟩
  rfl

theorem stationaryARightOne (L R : List Bool) :
    run0 stationary 1 ⟨0,[true]++L,[true]++R⟩ =
      some ⟨0,[true,true]++L,R⟩ := by
  rfl

theorem stationaryARightMany (n : Nat) (L R : List Bool) :
    run0 stationary n ⟨0,[true]++L,rep [true] n++R⟩ =
      some ⟨0,[true]++rep [true] n++L,R⟩ := by
  have h := sweepR stationary 0 [true] [] [true] [true] 1
    stationaryARightOne n L R
  simpa only [List.nil_append,Nat.one_mul,List.append_assoc] using h

theorem stationaryFinal (k : Nat) :
    run0 stationary 1
      ⟨0,[true]++rep [true] k++[true],[false,false,false,false]⟩ =
      some (stationaryWord (k+1)) := by
  simp [stationaryWord,stationary,run0,step0,move0,rep,rep_snoc,
        List.append_assoc]

theorem stationaryGrowth (k : Nat) :
    run0 stationary (stationaryCost k) (stationaryWord k) =
      some (stationaryWord (k+1)) := by
  have h0 := stationaryTurn (rep [true] (k+1))
  have h1 := stationaryELeftMany (k+1) [] [false,false,false,false]
  have h1' : run0 stationary (k+1)
      ⟨4,rep [true] (k+1),[false,false,false,false]⟩ =
      some ⟨4,[],rep [true] (k+1)++[false,false,false,false]⟩ := by
    simpa only [List.append_nil] using h1
  have h2 := stationaryEToA k
  have h3 := stationaryARightMany k [true] [false,false,false,false]
  have h3' : run0 stationary k
      ⟨0,[true,true],rep [true] k++[false,false,false,false]⟩ =
      some ⟨0,[true]++rep [true] k++[true],[false,false,false,false]⟩ := by
    simpa only [List.cons_append,List.nil_append,List.append_assoc] using h3
  have h4 := stationaryFinal k
  have H := join0 (join0 (join0 (join0 h0 h1') h2) h3') h4
  have ht : 9+(k+1)+1+k+1 = stationaryCost k := by
    unfold stationaryCost
    omega
  simpa only [stationaryWord,ht] using H

theorem stationary_never (m : Machine)
    (hm : compatible stationary m) : NeverHalts m := by
  exact never_of_growth stationary stationaryWord 10 stationaryCost
    stationaryFirst (by intro k; unfold stationaryCost; omega)
    stationaryGrowth m hm

#print axioms stationaryFirst
#print axioms stationaryTurn
#print axioms stationaryELeftMany
#print axioms stationaryEToA
#print axioms stationaryARightMany
#print axioms stationaryFinal
#print axioms stationaryGrowth
#print axioms stationary_never
end BB6.Agent40Raw34PairQuadratic
