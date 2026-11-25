import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent4Raw58RD1892
open BB6Coverage Agent31Pump Agent50Zipper

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨true,true,4⟩)
  | _,_ => none

def sentinel : List Bool := [false,false,true,true]
def E (k : Nat) (R : List Bool) : Z0 :=
  ⟨4,false :: true :: (rep [true,true] k ++ sentinel),R⟩

def C (k : Nat) (R : List Bool) : Z0 :=
  ⟨2,rep [true,true] k ++ sentinel,R⟩

inductive Code : List Bool → Prop
  | nil : Code []
  | single (b : Bool) : Code [b]
  | pair (b : Bool) (r : List Bool) : Code r → Code (b::false::r)

theorem zeros (k : Nat) (r : List Bool) (h : Code r) :
    Code (rep [false,false] k ++ r) := by
  induction k with
  | zero => exact h
  | succ k ih => exact Code.pair false _ ih

theorem carry (k : Nat) (r : List Bool) :
    run0 table 2 (E k (true::false::r)) = some (E (k+1) r) := by rfl

theorem carry_single (k : Nat) :
    run0 table 2 (E k [true]) = some (E (k+1) []) := by rfl

theorem flip_start (k : Nat) (r : List Bool) :
    run0 table 2 (E k (false::r)) = some (C (k+1) (true::r)) := by rfl

theorem flip_nil_start (k : Nat) :
    run0 table 2 (E k []) = some (C (k+1) [true]) := by rfl

theorem clearPair (L R : List Bool) :
    run0 table 2 ⟨2,[]++[true,true]++L,[]++R⟩ =
      some ⟨2,[]++L,[]++[false,false]++R⟩ := by rfl

theorem clear (k : Nat) (r : List Bool) :
    run0 table (2*k) (C k r) = some (C 0 (rep [false,false] k ++ r)) := by
  simpa only [C,rep,List.nil_append] using
    (sweepL table 2 [] [] [true,true] [false,false] 2 clearPair k sentinel r)

theorem reset (r : List Bool) :
    run0 table 8 (C 0 (false::false::r)) = some (E 0 r) := by rfl

theorem reset_flip (k : Nat) (r : List Bool) :
    run0 table (2*(k+1)+8) (C (k+1) (true::r)) =
      some (E 0 (rep [false,false] k ++ true::r)) := by
  exact join0 (clear (k+1) (true::r)) (reset (rep [false,false] k ++ true::r))

theorem flip (k : Nat) (r : List Bool) :
    run0 table (2+2*(k+1)+8) (E k (false::r)) =
      some (E 0 (rep [false,false] k ++ true::r)) := by
  have h := join0 (flip_start k r) (reset_flip k r)
  simpa only [Nat.add_assoc] using h

theorem flip_nil (k : Nat) :
    run0 table (2+2*(k+1)+8) (E k []) =
      some (E 0 (rep [false,false] k ++ [true])) := by
  have h := join0 (flip_nil_start k) (reset_flip k [])
  simpa only [Nat.add_assoc] using h

theorem returns (k : Nat) (r : List Bool) (hr : Code r) :
    ∃ t s, 0 < t ∧ Code s ∧ run0 table t (E k r) = some (E 0 s) := by
  induction hr generalizing k with
  | nil => exact ⟨_,_,by omega,zeros k _ (Code.single true),flip_nil k⟩
  | single b =>
    cases b with
    | false => exact ⟨_,_,by omega,zeros k _ (Code.single true),flip k []⟩
    | true =>
      exact ⟨_,_,by omega,zeros (k+1) _ (Code.single true),join0 (carry_single k) (flip_nil (k+1))⟩
  | pair b r h ih =>
    cases b with
    | false => exact ⟨_,_,by omega,zeros k _ (Code.pair true r h),flip k (false::r)⟩
    | true =>
      obtain ⟨t,s,ht,hs,hret⟩ := ih (k+1)
      exact ⟨2+t,s,by omega,hs,join0 (carry k r) hret⟩

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (E 0 []) := by rfl

theorem arbitrary (n : Nat) : ∃ t r, n ≤ t ∧ Code r ∧ run0 table t ⟨0,[],[]⟩ = some (E 0 r) := by
  induction n with
  | zero => exact ⟨15,[],by omega,Code.nil,entry⟩
  | succ n ih =>
    obtain ⟨t,r,ht,hr,hh⟩ := ih
    obtain ⟨u,s,hu,hs,hret⟩ := returns 0 r hr
    exact ⟨t+u,s,by omega,hs,join0 hh hret⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,r,ht,_,hr⟩ := arbitrary n
  have hz : (zrun table t Agent31Pump.start).map project = some (E 0 r) :=
    (run_project table t Agent31Pump.start).trans hr
  cases h : zrun table t Agent31Pump.start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound table m hm t Agent31Pump.start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms arbitrary
#print axioms never
end BB6Coverage.Agent4Raw58RD1892
