import ReturnInvariant
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw111TripleCounter
open BB6Coverage

-- 1RB---_1RC1LF_0RD0RF_1LD1RE_1LA0RC_0RE0LD
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨false,true,4⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

abbrev Z : List Bool := [false,false,false]
abbrev O : List Bool := [true,true,true]
abbrev S : List Bool := [false,false,true,true]
def f (b : Bool) (n : Nat) (R : List Bool) : Z0 :=
  ⟨5,b::(rep Z n++S),R⟩
def e (n : Nat) : Z0 := ⟨4,[false,false]++(rep Z n++S),[]⟩

inductive Good : List Bool → Prop
  | nil : Good []
  | stop : Good [true]
  | more (b : Bool) {R} : Good R → Good (true::true::b::R)

theorem ones (n : Nat) (R : List Bool) (h : Good R) :
    Good (rep O n++R) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    simpa only [rep,O,List.cons_append,List.nil_append] using Good.more true ih

theorem fZeroNil (n : Nat) : run0 table 1 (f false n []) = some (e n) := by rfl
theorem eReturn (n : Nat) : run0 table 3 (e n) = some (f true n [true]) := by rfl
theorem fZeroMore (b : Bool) (n : Nat) (R : List Bool) :
    run0 table 3 (f false n (true::true::b::R)) = some (f b (n+1) R) := by rfl
theorem fOneSmall (R : List Bool) :
    run0 table 6 (f true 0 R) = some (f false 0 R) := by rfl

theorem dLocal (L R : List Bool) : run0 table 3 ⟨3,Z++L,R⟩ =
    some ⟨3,L,O++R⟩ := by rfl
theorem fOneEntry (n : Nat) (R : List Bool) :
    run0 table 1 (f true (n+1) R) =
      some ⟨3,rep Z n ++ (Z++S),false::R⟩ := by
  have hz : Z++(rep Z n++S) = rep Z n++(Z++S) := by
    simpa only [List.append_assoc] using congrArg (· ++ S) (rep_snoc Z n).symm
  have h : run0 table 1 (f true (n+1) R) =
      some ⟨3,Z++(rep Z n++S),false::R⟩ := by rfl
  rw [hz] at h
  exact h
theorem dOneExit (R : List Bool) :
    run0 table 8 ⟨3,Z++S,R⟩ =
      some (f true 0 (true::true::R)) := by rfl

theorem one_prefix (n : Nat) (R : List Bool) :
    true::(rep O n++R) = rep O n++true::R := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rep,List.append_assoc,List.cons_append]
    exact congrArg (fun w => true::true::true::w) ih

theorem fOneLarge (n : Nat) (R : List Bool) :
    run0 table (1+3*n+8) (f true (n+1) R) =
      some (f true 0 (rep O n++true::true::false::R)) := by
  have h1 := fOneEntry n R
  have h2 := sweepL table 3 [] [] Z O 3 dLocal n (Z++S) (false::R)
  simp only [List.nil_append] at h2
  have H := join0 (join0 h1 h2) (dOneExit (rep O n++false::R))
  rw [one_prefix n (false::R),one_prefix n (true::false::R)] at H
  exact H

theorem fStopEntry (n : Nat) :
    run0 table 3 (f false n [true]) =
      some ⟨3,rep Z n++(Z++Z++[true,true]),[]⟩ := by
  have hz : Z++(rep Z n++(Z++[true,true])) =
      rep Z n++(Z++(Z++[true,true])) := by
    simpa only [List.append_assoc] using congrArg (· ++ (Z++[true,true])) (rep_snoc Z n).symm
  have h : run0 table 3 (f false n [true]) =
      some ⟨3,Z++(rep Z n++(Z++[true,true])),[]⟩ := by rfl
  rw [hz] at h
  simpa only [List.append_assoc] using h
theorem dStopExit (R : List Bool) :
    run0 table 9 ⟨3,Z++Z++[true,true],R⟩ = some (f true 0 (O++R)) := by rfl
theorem fStop (n : Nat) :
    run0 table (3+3*n+9) (f false n [true]) =
      some (f true 0 (rep O (n+1))) := by
  have h1 := fStopEntry n
  have h2 := sweepL table 3 [] [] Z O 3 dLocal n (Z++Z++[true,true]) []
  simp only [List.nil_append,List.append_nil] at h2
  have H := join0 (join0 h1 h2) (dStopExit (rep O n))
  simpa only [rep] using H

inductive Invariant : Z0 → Prop
  | atF (b : Bool) (n : Nat) {R} : Good R → Invariant (f b n R)
  | atE (n : Nat) : Invariant (e n)

theorem returns (c : Z0) (h : Invariant c) :
    ∃ k d, 0 < k ∧ run0 table k c = some d ∧ Invariant d := by
  cases h with
  | atE n => exact ⟨3,_,by decide,eReturn n,.atF true n .stop⟩
  | atF b n h =>
    cases b with
    | false =>
      cases h with
      | nil => exact ⟨1,_,by decide,fZeroNil n,.atE n⟩
      | stop =>
        exact ⟨3+3*n+9,_,by omega,fStop n,.atF true 0
          (by simpa only [List.append_nil] using ones (n+1) [] Good.nil)⟩
      | more b h => exact ⟨3,_,by decide,fZeroMore b n _, .atF b (n+1) h⟩
    | true =>
      cases n with
      | zero => exact ⟨6,_,by decide,fOneSmall _,.atF false 0 h⟩
      | succ n => exact ⟨1+3*n+8,_,by omega,fOneLarge n _,.atF true 0
          (ones n _ (.more false h))⟩

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (f false 0 []) := by rfl
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_return table Invariant 8 (f false 0 []) entry (.atF false 0 .nil) returns m hm

#print axioms never
end BB6Coverage.Agent31Pump.Raw111TripleCounter
