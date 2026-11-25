import ReturnInvariant

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6Coverage.Agent31Pump.Raw111Triplet
open BB6Coverage

-- 1RB0LD_1RC1LE_0RD0RF_1LD1RE_---0RC_0RC0RA
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,true,0⟩)
  | _,_ => none

abbrev Z : List Bool := [false,false,false]
abbrev O : List Bool := [true,true,true]
abbrev S : List Bool := [true,true]
def a (b : Bool) (n : Nat) (R : List Bool) : Z0 :=
  ⟨0,b::(Z ++ rep Z n ++ S),R⟩
def f (n : Nat) : Z0 := ⟨5,Z ++ rep Z n ++ S,[]⟩

inductive Good : List Bool → Prop
  | stop : Good [true]
  | more (b : Bool) {R} : Good R → Good (true::true::b::R)

theorem onesPrefix (n : Nat) (R : List Bool) (h : Good R) :
    Good (rep O n ++ R) := by
  induction n with
  | zero => exact h
  | succ n ih => simpa only [rep,O,List.cons_append,List.nil_append,List.append_assoc] using Good.more true ih

theorem shiftOne (n : Nat) (R : List Bool) :
    true::(rep O n ++ R) = rep O n ++ true::R := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rep,List.append_assoc,List.cons_append]
    exact congrArg (fun w => true::true::true::w) ih

theorem shiftTwo (n : Nat) (R : List Bool) :
    true::true::(rep O n ++ R) = rep O n ++ true::true::R := by
  rw [shiftOne n R,shiftOne n (true::R)]

theorem dSweep (L R : List Bool) :
    run0 table 3 ⟨3,Z++L,R⟩ = some ⟨3,L,O++R⟩ := by rfl

theorem dSweepFramed (L R : List Bool) :
    run0 table 3 ⟨3,[false,false]++Z++L,R⟩ =
      some ⟨3,[false,false]++L,O++R⟩ := by rfl

theorem fEntry (n : Nat) :
    run0 table 2 (f n) = some ⟨3,[false,false]++Z++rep Z n++S,[]⟩ := by rfl
theorem fExit (R : List Bool) :
    run0 table 9 ⟨3,[false,false]++Z++S,R⟩ =
      some (a true 0 (true::R)) := by rfl

theorem fReturn (n : Nat) :
    run0 table (2+3*n+9) (f n) =
      some (a true 0 (rep O n ++ [true])) := by
  have h1 : run0 table 2 (f n) =
      some ⟨3,[false,false]++rep Z n++Z++S,[]⟩ := by
    have hz : rep Z n ++ (Z ++ S) = Z ++ (rep Z n ++ S) := by
      simpa only [List.append_assoc] using congrArg (· ++ S) (rep_snoc Z n)
    simpa only [List.append_assoc, hz] using fEntry n
  have h2 := sweepL table 3 [false,false] [] Z O 3 dSweepFramed n (Z++S) []
  simp only [List.nil_append,List.append_nil,List.append_assoc] at h2
  simp only [List.append_assoc] at h1
  have h3 := fExit (rep O n)
  simp only [List.append_assoc] at h3
  have H := join0 (join0 h1 h2) h3
  rw [show true::rep O n = rep O n ++ [true] by
    simpa only [List.append_nil] using shiftOne n []] at H
  exact H

theorem aZeroMore (b : Bool) (n : Nat) (R : List Bool) :
    run0 table 5 (a false n (true::true::b::R)) =
      some (a b (n+1) R) := by rfl
theorem aZeroStop (n : Nat) :
    run0 table 4 (a false n [true]) = some (f (n+1)) := by rfl
theorem aOneSmall (R : List Bool) :
    run0 table 8 (a true 0 R) = some (a false 0 R) := by rfl

theorem aOneEntry (L R : List Bool) :
    run0 table 1 ⟨0,true::L,R⟩ = some ⟨3,L,false::R⟩ := by rfl
theorem aOneExit (R : List Bool) :
    run0 table 10 ⟨3,Z++Z++S,R⟩ =
      some (a true 0 (true::true::R)) := by rfl

theorem aOneLarge (n : Nat) (R : List Bool) :
    run0 table (1+3*n+10) (a true (n+1) R) =
      some (a true 0 (rep O n ++ true::true::false::R)) := by
  have h1 : run0 table 1 (a true (n+1) R) =
      some ⟨3,rep Z n++Z++Z++S,false::R⟩ := by
    simpa only [a,rep,List.append_assoc,rep_snoc Z n] using
      aOneEntry (Z++Z++rep Z n++S) R
  have h2 := sweepL table 3 [] [] Z O 3 dSweep n (Z++Z++S) (false::R)
  simp only [List.nil_append,List.append_assoc] at h2
  simp only [List.append_assoc] at h1
  have h3 := aOneExit (rep O n ++ false::R)
  simp only [List.append_assoc] at h3
  have H := join0 (join0 h1 h2) h3
  rw [shiftTwo n (false::R)] at H
  exact H

inductive Invariant : Z0 → Prop
  | boundary (n : Nat) : Invariant (f n)
  | frame (b : Bool) (n : Nat) {R} : Good R → Invariant (a b n R)

theorem returns (c : Z0) (h : Invariant c) :
    ∃ k d, 0 < k ∧ run0 table k c = some d ∧ Invariant d := by
  cases h with
  | boundary n =>
    exact ⟨2+3*n+9,_,by omega,fReturn n,
      Invariant.frame true 0 (onesPrefix n _ Good.stop)⟩
  | frame b n hR =>
    cases b with
    | false =>
      cases hR with
      | stop => exact ⟨4,_,by decide,aZeroStop n,Invariant.boundary (n+1)⟩
      | more b h => exact ⟨5,_,by decide,aZeroMore b n _,Invariant.frame b (n+1) h⟩
    | true =>
      cases n with
      | zero => exact ⟨8,_,by decide,aOneSmall _,Invariant.frame false 0 hR⟩
      | succ n => exact ⟨1+3*n+10,_,by omega,aOneLarge n _,
          Invariant.frame true 0 (onesPrefix n _ (Good.more false hR))⟩

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (f 0) := by rfl
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_return table Invariant 8 (f 0) entry (Invariant.boundary 0) returns m hm

#print axioms never
end BB6Coverage.Agent31Pump.Raw111Triplet
