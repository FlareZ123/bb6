import SweepPumping

namespace BB6.Agent10Raw108RD48
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- 1RB---_1RC0RD_0RD1RA_1LD1RE_0LF1LB_1LB1LE. -/
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev E (L R : List Bool) : Z0 := ⟨4,L,R⟩
abbrev P : List Bool := [true,true]
abbrev Q : List Bool := [true,false]

def cfg (k n : Nat) : Z0 := A (false::rep P (k+1)) (rep Q (n+1))

theorem transfer (L R : List Bool) :
    run0 table 20 (A (false::true::true::L) (Q++Q++R)) =
      some (A (false::true::true::true::true::L) (Q++R)) := by rfl

theorem advance (k n : Nat) :
    run0 table 20 (cfg k (n+1)) = some (cfg (k+1) n) := by
  exact transfer (rep P k) (rep Q n)

theorem reset_start (L : List Bool) :
    run0 table 21 (A (false::true::true::L) Q) = some (E L (rep Q 3)) := by rfl

theorem return_four (L R : List Bool) :
    run0 table 16 (E (P++P++L) (Q++R)) =
      some (E L (Q++Q++Q++R)) := by rfl

theorem return_zero (R : List Bool) :
    run0 table 4 (E [] (Q++R)) = some (A [false,true,true] (Q++R)) := by rfl

theorem return_two (R : List Bool) :
    run0 table 12 (E P (Q++R)) = some (A [false,true,true] (Q++R)) := by rfl

theorem finish (k n : Nat) : ∃ t m,
    run0 table t (E (rep P k) (rep Q (n+1))) = some (cfg 0 m) := by
  induction k using Nat.strongRecOn generalizing n with
  | ind k ih =>
    cases k with
    | zero => exact ⟨4,n,return_zero (rep Q n)⟩
    | succ k =>
      cases k with
      | zero => exact ⟨12,n,return_two (rep Q n)⟩
      | succ k =>
        obtain ⟨t,m,h⟩ := ih k (by omega) (n+2)
        have h₁ : run0 table 16 (E (rep P (k+1+1)) (rep Q (n+1))) =
          some (E (rep P k) (rep Q (n+2+1))) := by
          exact return_four (rep P k) (rep Q n)
        exact ⟨16+t,m,join0 h₁ h⟩

theorem epoch (s : Nat × Nat) : ∃ (t : Nat) (s' : Nat × Nat),
    0 < t ∧ run0 table t (cfg s.1 s.2) = some (cfg s'.1 s'.2) := by
  rcases s with ⟨k,n⟩
  cases n with
  | zero =>
    obtain ⟨t,m,h⟩ := finish k 2
    exact ⟨21+t,⟨0,m⟩,by omega,join0 (reset_start (rep P k)) h⟩
  | succ n => exact ⟨20,⟨k+1,n⟩,by omega,advance k n⟩

noncomputable def next (s : Nat × Nat) : Nat × Nat := (epoch s).choose_spec.choose
noncomputable def sections : Nat → Nat × Nat
  | 0 => (0,1)
  | n+1 => next (sections n)
noncomputable def family (n : Nat) : Z0 := cfg (sections n).1 (sections n).2
noncomputable def cost (n : Nat) : Nat := (epoch (sections n)).choose

theorem entry : run0 table 24 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem cost_pos (n : Nat) : 0 < cost n := (epoch (sections n)).choose_spec.choose_spec.1
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) :=
  (epoch (sections n)).choose_spec.choose_spec.2

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 24 cost entry cost_pos growth m hm

#print axioms entry
#print axioms finish
#print axioms epoch
#print axioms growth
#print axioms never
end BB6.Agent10Raw108RD48
