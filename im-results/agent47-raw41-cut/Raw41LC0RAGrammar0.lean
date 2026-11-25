import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw41.LC0RA0
open BB6Coverage BB6Coverage.Agent31Pump
-- 1RB0LC_1RC0LE_0RD0RA_1LD1RA_1LF0LE_---0LB
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

def U : List Bool := [true]

/-- Terminal singleton 1; all preceding runs of 1s have length at least two. -/
inductive GoodTail : List Bool → Prop
  | last : GoodTail [true]
  | more (n : Nat) (xs : List Bool) (h : GoodTail xs) :
      GoodTail (rep U (n+2) ++ false::xs)

/-- In A, the head is a zero, followed by either 10 and a tail, or by
    0 and a nonterminal tail. The latter restriction is essential. -/
inductive ALeft : List Bool → Prop
  | one (xs : List Bool) (h : GoodTail xs) : ALeft (true::false::xs)
  | zero (xs : List Bool) (h : GoodTail xs) (hne : xs ≠ [true]) : ALeft (false::xs)

/-- No consecutive ones; either end symbol is allowed. -/
inductive RightWord : List Bool → Prop
  | nil : RightWord []
  | zero (xs : List Bool) (h : RightWord xs) : RightWord (false::xs)
  | last : RightWord [true]
  | oneZero (xs : List Bool) (h : RightWord xs) : RightWord (true::false::xs)

inductive Inv : Z0 → Prop
  | a (L R : List Bool) (hl : ALeft L) (hr : RightWord R) : Inv ⟨0,false::L,R⟩
  | e (n : Nat) (xs R : List Bool) (hl : GoodTail xs) (hr : RightWord R) :
      Inv ⟨4,rep U n ++ false::xs,false::R⟩
  | special (xs R : List Bool) (hl : GoodTail xs) (hne : xs ≠ [true]) (hr : RightWord R) :
      Inv ⟨4,[true,false,true,false]++xs,false::R⟩

theorem extendOne (xs : List Bool) (h : GoodTail xs) (hne : xs ≠ [true]) : GoodTail (true::xs) := by
  cases h with
  | last => exact False.elim (hne rfl)
  | more n xs h => exact GoodTail.more (n+1) xs h

theorem extendTwo (L : List Bool) (h : ALeft L) : GoodTail (true::true::L) := by
  cases h with
  | one xs h => exact GoodTail.more 1 xs h
  | zero xs h hn => exact GoodTail.more 0 xs h

theorem eAfterOne (L R : List Bool) (hl : ALeft L) (hr : RightWord R) : Inv ⟨4,true::L,false::R⟩ := by
  cases hl with
  | one xs h => exact Inv.e 2 xs R h hr
  | zero xs h hn => exact Inv.e 1 xs R h hr

theorem eAfterThree (L R : List Bool) (hl : ALeft L) (hr : RightWord R) : Inv ⟨4,[true,false,true]++L,false::R⟩ := by
  cases hl with
  | one xs h => exact Inv.e 1 _ R (GoodTail.more 0 xs h) hr
  | zero xs h hn => exact Inv.special xs R h hn hr

theorem aAfterTwo (L R : List Bool) (hl : ALeft L) (hr : RightWord R) : Inv ⟨0,[false,false,true,true]++L,R⟩ :=
  Inv.a _ R (ALeft.zero _ (extendTwo L hl) (by simp)) hr

theorem aAfterThree (L R : List Bool) (hl : ALeft L) (hr : RightWord R) : Inv ⟨0,[false,true,false,true,true]++L,R⟩ :=
  Inv.a _ R (ALeft.one _ (extendTwo L hl)) hr

-- A sweeps right until a 1, or returns left after three consecutive blanks.
theorem a1 (L R : List Bool) : run0 table 2 ⟨0,false::L,true::R⟩ = some ⟨4,true::L,false::R⟩ := by rfl
theorem a01 (L R : List Bool) : run0 table 3 ⟨0,false::L,false::true::false::R⟩ = some ⟨0,[false,false,true,true]++L,R⟩ := by rfl
theorem a01end (L : List Bool) : run0 table 3 ⟨0,false::L,[false,true]⟩ = some ⟨0,[false,false,true,true]++L,[]⟩ := by rfl
theorem a001 (L R : List Bool) : run0 table 4 ⟨0,false::L,false::false::true::false::R⟩ = some ⟨0,[false,true,false,true,true]++L,R⟩ := by rfl
theorem a001end (L : List Bool) : run0 table 4 ⟨0,false::L,[false,false,true]⟩ = some ⟨0,[false,true,false,true,true]++L,[]⟩ := by rfl
theorem a000 (L R : List Bool) : run0 table 10 ⟨0,false::L,false::false::false::R⟩ = some ⟨4,[true,false,true]++L,false::R⟩ := by rfl
theorem a0end (L : List Bool) : run0 table 10 ⟨0,false::L,[]⟩ = some ⟨4,[true,false,true]++L,[false]⟩ := by rfl
theorem a00end (L : List Bool) : run0 table 10 ⟨0,false::L,[false]⟩ = some ⟨4,[true,false,true]++L,[false]⟩ := by rfl
theorem a000end (L : List Bool) : run0 table 10 ⟨0,false::L,[false,false]⟩ = some ⟨4,[true,false,true]++L,[false]⟩ := by rfl

def Returns (z : Z0) : Prop := ∃ t z', 0 < t ∧ run0 table t z = some z' ∧ Inv z'

theorem progressA (L R : List Bool) (hl : ALeft L) (hr : RightWord R) : Returns ⟨0,false::L,R⟩ := by
  cases hr with
  | nil => exact ⟨10,_,by decide,a0end L,eAfterThree L [] hl RightWord.nil⟩
  | last => exact ⟨2,_,by decide,a1 L [],eAfterOne L [] hl RightWord.nil⟩
  | oneZero R h => exact ⟨2,_,by decide,a1 L (false::R),eAfterOne L _ hl (RightWord.zero R h)⟩
  | zero R h =>
    cases h with
    | nil => exact ⟨10,_,by decide,a00end L,eAfterThree L [] hl RightWord.nil⟩
    | last => exact ⟨3,_,by decide,a01end L,aAfterTwo L [] hl RightWord.nil⟩
    | oneZero R h => exact ⟨3,_,by decide,a01 L R,aAfterTwo L R hl h⟩
    | zero R h =>
      cases h with
      | nil => exact ⟨10,_,by decide,a000end L,eAfterThree L [] hl RightWord.nil⟩
      | last => exact ⟨4,_,by decide,a001end L,aAfterThree L [] hl RightWord.nil⟩
      | oneZero R h => exact ⟨4,_,by decide,a001 L R,aAfterThree L R hl h⟩
      | zero R h => exact ⟨10,_,by decide,a000 L R,eAfterThree L R hl h⟩

-- E scans a run of 1s, then passes two 1s or turns at the terminal singleton.
theorem e1 (L R : List Bool) : run0 table 1 ⟨4,true::L,false::R⟩ = some ⟨4,L,false::false::R⟩ := by rfl
theorem e011 (L R : List Bool) : run0 table 3 ⟨4,false::true::true::L,false::R⟩ = some ⟨4,L,[false,false,true,false]++R⟩ := by rfl
theorem e01 (R : List Bool) : run0 table 5 ⟨4,[false,true],false::R⟩ = some ⟨0,[false,true,false,true],R⟩ := by rfl
theorem e1010 (L R : List Bool) : run0 table 6 ⟨4,[true,false,true,false]++L,false::R⟩ = some ⟨0,[false,true,false,true]++L,false::R⟩ := by rfl
theorem progressE (n : Nat) (xs R : List Bool) (hl : GoodTail xs) (hr : RightWord R) : Returns ⟨4,rep U n ++ false::xs,false::R⟩ := by
  cases n with
  | succ n => exact ⟨1,_,by decide,e1 _ R,Inv.e n xs _ hl (RightWord.zero R hr)⟩
  | zero =>
    cases hl with
    | last => exact ⟨5,_,by decide,e01 R,Inv.a _ R (ALeft.one [true] GoodTail.last) hr⟩
    | more n xs h =>
      exact ⟨3,_,by decide,e011 _ R,Inv.e n xs _ h (RightWord.zero _ (RightWord.oneZero R hr))⟩

theorem progressSpecial (xs R : List Bool) (hl : GoodTail xs) (hne : xs ≠ [true]) (hr : RightWord R) : Returns ⟨4,[true,false,true,false]++xs,false::R⟩ :=
  ⟨6,_,by decide,e1010 xs R,Inv.a _ _ (ALeft.one _ (extendOne xs hl hne)) (RightWord.zero R hr)⟩

theorem progress (z : Z0) (hz : Inv z) : Returns z := by
  cases hz with
  | a L R hl hr => exact progressA L R hl hr
  | e n xs R hl hr => exact progressE n xs R hl hr
  | special xs R hl hn hr => exact progressSpecial xs R hl hn hr

theorem entry : run0 table 10 ⟨0,[],[]⟩ = some ⟨4,[true,false,true],[false]⟩ := by rfl
theorem entryInv : Inv ⟨4,[true,false,true],[false]⟩ := Inv.e 1 [true] [] GoodTail.last RightWord.nil

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  have arbitrary : ∀ k : Nat, ∃ t z, k ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some z ∧ Inv z := by
    intro k
    induction k with
    | zero => exact ⟨10,_,by decide,entry,entryInv⟩
    | succ k ih =>
      obtain ⟨t,z,ht,hr,hz⟩ := ih
      obtain ⟨s,z',hs,he,hz'⟩ := progress z hz
      exact ⟨t+s,z',by omega,join0 hr he,hz'⟩
  intro n
  obtain ⟨t,z,ht,hr,_⟩ := arbitrary n
  have hz : (Agent50Zipper.zrun table t BB6Coverage.Agent31Pump.start).map project = some z :=
    (run_project table t BB6Coverage.Agent31Pump.start).trans hr
  cases h : Agent50Zipper.zrun table t BB6Coverage.Agent31Pump.start with
  | none => simp [h] at hz
  | some z =>
    have H := Agent50Zipper.zrun_sound table m hm t BB6Coverage.Agent31Pump.start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl
#print axioms progress
#print axioms never
end BB6.Agent47Raw41.LC0RA0
