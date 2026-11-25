import ReturnInvariant

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6Coverage.Agent31Pump.Raw111QuadCounter
open BB6Coverage

-- 1RB0LF_1RC---_0RD1LF_1LD1RE_0RB0RC_0LA0RF
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨false,true,5⟩)
  | _,_ => none

abbrev Z : List Bool := [false,false,false,false]
abbrev O : List Bool := [true,false,false,false]
abbrev P : List Bool := [true,false,true,false]
abbrev S : List Bool := [true,false,true,true]
def a (R : List Bool) : Z0 := ⟨0,[false],[false,false]++R⟩
def e (n : Nat) (R : List Bool) : Z0 :=
  ⟨4,false::(rep P n ++ S),[false,false]++R⟩
def boundary (n : Nat) : Z0 := ⟨4,false::(rep P n ++ S),[]⟩

inductive Good : List Bool → Prop
  | stop : Good [true]
  | zero {R} : Good R → Good (Z++R)
  | one {R} : Good R → Good (O++R)

theorem zeros (n : Nat) (R : List Bool) (h : Good R) :
    Good (rep Z n ++ R) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    simpa only [rep,List.append_assoc] using Good.zero ih

theorem aZero (R : List Bool) : run0 table 12 (a (Z++R)) = some (a (O++R)) := by rfl
theorem aOne (R : List Bool) : run0 table 4 (a (O++R)) = some (e 0 R) := by rfl
theorem aStop : run0 table 4 (a [true]) = some (boundary 0) := by rfl
theorem eOne (n : Nat) (R : List Bool) :
    run0 table 4 (e n (O++R)) = some (e (n+1) R) := by rfl
theorem eStop (n : Nat) :
    run0 table 4 (e n [true]) = some (boundary (n+1)) := by rfl

def f (n : Nat) (R : List Bool) : Z0 :=
  ⟨5,[false,true,false]++(rep P n++S),R⟩

theorem eZero (n : Nat) (R : List Bool) :
    run0 table 8 (e n (Z++R)) = some (f n (O++R)) := by rfl
theorem boundaryEntry (n : Nat) :
    run0 table 8 (boundary n) = some (f n [true]) := by rfl
theorem localF (L R : List Bool) :
    run0 table 4 ⟨5,[false,true,false]++P++L,R⟩ =
      some ⟨5,[false,true,false]++L,Z++R⟩ := by rfl
theorem exitF (R : List Bool) : run0 table 8 (f 0 R) =
    some (a (Z++R)) := by rfl
theorem fReturn (n : Nat) (R : List Bool) :
    run0 table (4*n+8) (f n R) = some (a (rep Z (n+1)++R)) := by
  have h := sweepL table 5 [false,true,false] [] P Z 4 localF n S R
  have h1 : run0 table (4*n) (f n R) = some (f 0 (rep Z n++R)) := by
    simpa only [f,rep,List.nil_append,List.append_assoc] using h
  have H := join0 h1 (exitF (rep Z n++R))
  simpa only [rep,List.append_assoc] using H

inductive Invariant : Z0 → Prop
  | atA {R} : Good R → Invariant (a R)
  | atE (n : Nat) {R} : Good R → Invariant (e n R)
  | endE (n : Nat) : Invariant (boundary n)

theorem returns (c : Z0) (h : Invariant c) :
    ∃ k d, 0 < k ∧ run0 table k c = some d ∧ Invariant d := by
  cases h with
  | atA h =>
    cases h with
    | stop => exact ⟨4,_,by decide,aStop,.endE 0⟩
    | zero h => exact ⟨12,_,by decide,aZero _,.atA (.one h)⟩
    | one h => exact ⟨4,_,by decide,aOne _,.atE 0 h⟩
  | atE n h =>
    cases h with
    | stop => exact ⟨4,_,by decide,eStop n,.endE (n+1)⟩
    | one h => exact ⟨4,_,by decide,eOne n _,.atE (n+1) h⟩
    | zero h =>
      exact ⟨8+(4*n+8),_,by omega,join0 (eZero n _) (fReturn n _),
        .atA (zeros (n+1) _ (.one h))⟩
  | endE n =>
    exact ⟨8+(4*n+8),_,by omega,join0 (boundaryEntry n) (fReturn n _),
      .atA (zeros (n+1) _ .stop)⟩

theorem entry : run0 table 12 ⟨0,[],[]⟩ = some (a [true]) := by rfl
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_return table Invariant 12 (a [true]) entry (.atA .stop) returns m hm

#print axioms never
end BB6Coverage.Agent31Pump.Raw111QuadCounter
