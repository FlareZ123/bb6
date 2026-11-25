import SweepPumping
import Raw58Live

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent4Raw109RE238
open BB6Coverage Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,1⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def ones : List Bool := [true,true,true,true]
def zeros : List Bool := [false,false,false,false]
def sentinel : List Bool := [false,true,true,true,false]

def A (k : Nat) (r : List Bool) : Z0 :=
  ⟨0,true :: (rep ones k ++ sentinel),r⟩

def E (k : Nat) (r : List Bool) : Z0 :=
  ⟨4,r.headD false :: true :: (rep ones k ++ sentinel),r.tail⟩

inductive Code : List Bool → Prop
  | nil : Code []
  | single (b : Bool) : Code [b]
  | block (b : Bool) (r : List Bool) : Code r →
      Code (b::false::false::false::r)

theorem prefix_zeros (k : Nat) (r : List Bool) (h : Code r) :
    Code (rep zeros k ++ r) := by
  induction k with
  | zero => exact h
  | succ k ih => exact Code.block false _ ih

theorem enter (r : List Bool) :
    run0 table 3 (A 0 r) = some (E 0 r) := by
  cases r <;> rfl

theorem carry (k : Nat) (r : List Bool) :
    run0 table 8 (E k (true::false::false::false::r)) =
      some (E (k+1) r) := by rfl

theorem carry_single (k : Nat) :
    run0 table 8 (E k [true]) = some (E (k+1) []) := by rfl

theorem flip_start (k : Nat) (r : List Bool) :
    run0 table 1 (E k (false::r)) = some (A k (true::r)) := by rfl

theorem flip_nil_start (k : Nat) :
    run0 table 1 (E k []) = some (A k [true]) := by rfl

theorem clear4 (L R : List Bool) :
    run0 table 12 ⟨0,[true]++ones++L,R⟩ =
      some ⟨0,[true]++L,zeros++R⟩ := by rfl

theorem clear (k : Nat) (r : List Bool) :
    run0 table (12*k) (A k r) = some (A 0 (rep zeros k ++ r)) := by
  simpa only [A,rep,List.nil_append,List.cons_append,List.singleton_append] using
    (sweepL table 0 [true] [] ones zeros 12 clear4 k sentinel r)

theorem flip (k : Nat) (r : List Bool) :
    run0 table (1+12*k) (E k (false::r)) =
      some (A 0 (rep zeros k ++ true::r)) :=
  join0 (flip_start k r) (clear k (true::r))

theorem flip_nil (k : Nat) :
    run0 table (1+12*k) (E k []) =
      some (A 0 (rep zeros k ++ [true])) :=
  join0 (flip_nil_start k) (clear k [true])

theorem returnsE (k : Nat) (r : List Bool) (hr : Code r) :
    ∃ t s, 0 < t ∧ Code s ∧ run0 table t (E k r) = some (A 0 s) := by
  induction hr generalizing k with
  | nil => exact ⟨_,_,by omega,prefix_zeros k _ (Code.single true),flip_nil k⟩
  | single b =>
    cases b with
    | false => exact ⟨_,_,by omega,prefix_zeros k _ (Code.single true),flip k []⟩
    | true =>
      exact ⟨_,_,by omega,prefix_zeros (k+1) _ (Code.single true),
        join0 (carry_single k) (flip_nil (k+1))⟩
  | block b r h ih =>
    cases b with
    | false =>
      exact ⟨_,_,by omega,prefix_zeros k _ (Code.block true r h),
        flip k (false::false::false::r)⟩
    | true =>
      obtain ⟨t,s,ht,hs,hret⟩ := ih (k+1)
      exact ⟨8+t,s,by omega,hs,join0 (carry k r) hret⟩

theorem returns (r : List Bool) (hr : Code r) :
    ∃ t s, 0 < t ∧ Code s ∧ run0 table t (A 0 r) = some (A 0 s) := by
  obtain ⟨t,s,ht,hs,hret⟩ := returnsE 0 r hr
  exact ⟨3+t,s,by omega,hs,join0 (enter r) hret⟩

theorem entry : run0 table 30 ⟨0,[],[]⟩ = some (A 0 [true]) := by rfl

theorem arbitrary (n : Nat) :
    ∃ t r, n ≤ t ∧ Code r ∧ run0 table t ⟨0,[],[]⟩ = some (A 0 r) := by
  induction n with
  | zero => exact ⟨30,[true],by omega,Code.single true,entry⟩
  | succ n ih =>
    obtain ⟨t,r,ht,hr,hh⟩ := ih
    obtain ⟨u,s,hu,hs,hret⟩ := returns r hr
    exact ⟨t+u,s,by omega,hs,join0 hh hret⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table (fun n => by
    obtain ⟨t,r,ht,_,hr⟩ := arbitrary n
    exact ⟨t,A 0 r,ht,hr⟩) m hm

#print axioms arbitrary
#print axioms never
end BB6Coverage.Agent4Raw109RE238
