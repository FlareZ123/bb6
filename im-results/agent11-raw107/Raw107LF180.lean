import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10Raw107LF180
open BB6Coverage BB6Coverage.Agent31Pump

-- 1RB1LA_1RC0LF_0RD---_1LD1RE_1RC0RB_1LA0LA
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,2⟩)
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

inductive Digit where
  | zero | one | two
  deriving DecidableEq, Repr
inductive Mark where
  | one | two
  deriving DecidableEq, Repr

def payload : Digit → List Bool
  | .zero => []
  | .one => [true]
  | .two => [true,true]

def enc : List Digit → List Bool
  | [] => [false]
  | d::ds => false::false::(payload d ++ enc ds)

def stack : List Mark → List Bool
  | [] => [true,true]
  | .one::h => true::true::false::stack h
  | .two::h => true::false::true::false::stack h

def drain : List Mark → List Bool → List Bool
  | [], R => false::false::true::R
  | .one::h, R => drain h (false::false::true::R)
  | .two::h, R => drain h (false::false::false::false::R)

abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev C (h : List Mark) (R : List Bool) : Z0 := ⟨2,false::stack h,R⟩

theorem left_one (L R : List Bool) :
    run0 table 5 (A (true::true::false::L) R) =
      some (A L (false::false::true::R)) := by rfl

theorem left_two (L R : List Bool) :
    run0 table 8 (A (true::false::true::false::L) R) =
      some (A L (false::false::false::false::R)) := by rfl

theorem left_base (R : List Bool) :
    run0 table 5 (A [true,true] R) = some (A [] (false::false::true::R)) := by rfl

theorem drain_run (h : List Mark) (R : List Bool) :
    ∃ t, 0 < t ∧ run0 table t (A (stack h) R) = some (A [] (drain h R)) := by
  induction h generalizing R with
  | nil => exact ⟨5,by decide,left_base R⟩
  | cons a h ih =>
    cases a with
    | one =>
      obtain ⟨t,ht,hr⟩ := ih (false::false::true::R)
      exact ⟨5+t,by omega,join0 (left_one (stack h) R) hr⟩
    | two =>
      obtain ⟨t,ht,hr⟩ := ih (false::false::false::false::R)
      exact ⟨8+t,by omega,join0 (left_two (stack h) R) hr⟩

theorem drain_enc (h : List Mark) (ds : List Digit) :
    ∃ es, drain h (enc ds) = enc es := by
  induction h generalizing ds with
  | nil => exact ⟨.one::ds,rfl⟩
  | cons a h ih =>
    cases a with
    | one => exact ih (.one::ds)
    | two => exact ih (.zero::.zero::ds)

theorem drain_extra (h : List Mark) (ds : List Digit) :
    ∃ es, drain h (true::enc ds) = enc es := by
  cases h with
  | nil => exact ⟨.two::ds,rfl⟩
  | cons a h =>
    cases a with
    | one => exact drain_enc h (.two::ds)
    | two => exact drain_enc h (.zero::.one::ds)

theorem turn_raw (L R : List Bool) :
    run0 table 7 (⟨2,false::true::L,false::R⟩ : Z0) =
      some (A (true::L) (true::false::R)) := by rfl

theorem turn_empty_raw (L : List Bool) :
    run0 table 7 (⟨2,false::true::L,[]⟩ : Z0) =
      some (A (true::L) [true,false]) := by rfl

theorem turn (h : List Mark) (R : List Bool) :
    run0 table 7 (C h (false::R)) = some (A (stack h) (true::false::R)) := by
  cases h with
  | nil => rfl
  | cons a h => cases a <;> rfl

theorem turn_empty (h : List Mark) :
    run0 table 7 (C h []) = some (A (stack h) [true,false]) := by
  cases h with
  | nil => rfl
  | cons a h => cases a <;> rfl

theorem finish (h : List Mark) (ds : List Digit) :
    ∃ t es, 0 < t ∧ run0 table t (C h (enc ds)) = some (A [] (enc es)) := by
  have h1 : run0 table 7 (C h (enc ds)) = some (A (stack h) (true::enc ds)) := by
    cases ds with
    | nil => exact turn h []
    | cons d ds => exact turn h (false::payload d ++ enc ds)
  obtain ⟨t,ht,h2⟩ := drain_run h (true::enc ds)
  obtain ⟨es,he⟩ := drain_extra h ds
  rw [he] at h2
  exact ⟨7+t,es,by omega,join0 h1 h2⟩

theorem finish_empty (h : List Mark) :
    ∃ t es, 0 < t ∧ run0 table t (C h []) = some (A [] (enc es)) := by
  obtain ⟨t,ht,h2⟩ := drain_run h [true,false]
  obtain ⟨es,he⟩ := drain_extra h []
  change drain h [true,false] = enc es at he
  rw [he] at h2
  exact ⟨7+t,es,by omega,join0 (turn_empty h) h2⟩

theorem scan_one (h : List Mark) (R : List Bool) :
    run0 table 3 (C h (true::false::false::R)) = some (C (.one::h) R) := by rfl

theorem scan_two (h : List Mark) (R : List Bool) :
    run0 table 4 (C h (true::true::false::false::R)) = some (C (.two::h) R) := by rfl

theorem scan_one_end (h : List Mark) :
    run0 table 3 (C h [true,false]) = some (C (.one::h) []) := by rfl

theorem scan_two_end (h : List Mark) :
    run0 table 4 (C h [true,true,false]) = some (C (.two::h) []) := by rfl

theorem scan (ds : List Digit) (h : List Mark) (d : Digit) :
    ∃ t es, 0 < t ∧ run0 table t (C h (payload d ++ enc ds)) = some (A [] (enc es)) := by
  induction ds generalizing h d with
  | nil =>
    cases d with
    | zero => exact finish h []
    | one =>
      obtain ⟨t,es,ht,hr⟩ := finish_empty (.one::h)
      exact ⟨3+t,es,by omega,join0 (scan_one_end h) hr⟩
    | two =>
      obtain ⟨t,es,ht,hr⟩ := finish_empty (.two::h)
      exact ⟨4+t,es,by omega,join0 (scan_two_end h) hr⟩
  | cons e ds ih =>
    cases d with
    | zero => exact finish h (e::ds)
    | one =>
      obtain ⟨t,es,ht,hr⟩ := ih (.one::h) e
      exact ⟨3+t,es,by omega,join0 (scan_one h (payload e ++ enc ds)) hr⟩
    | two =>
      obtain ⟨t,es,ht,hr⟩ := ih (.two::h) e
      exact ⟨4+t,es,by omega,join0 (scan_two h (payload e ++ enc ds)) hr⟩

theorem epoch (ds : List Digit) :
    ∃ t es, 0 < t ∧ run0 table t (A [] (enc ds)) = some (A [] (enc es)) := by
  cases ds with
  | nil =>
    have h1 : run0 table 2 (A [] (enc [])) = some (C [] []) := by rfl
    obtain ⟨t,es,ht,h2⟩ := finish_empty []
    exact ⟨2+t,es,by omega,join0 h1 h2⟩
  | cons d ds =>
    have h1 : run0 table 2 (A [] (enc (d::ds))) = some (C [] (payload d ++ enc ds)) := by rfl
    obtain ⟨t,es,ht,h2⟩ := scan ds [] d
    exact ⟨2+t,es,by omega,join0 h1 h2⟩

noncomputable def epochCost (ds : List Digit) : Nat := (epoch ds).choose
noncomputable def next (ds : List Digit) : List Digit := (epoch ds).choose_spec.choose
noncomputable def digits : Nat → List Digit
  | 0 => [.two]
  | n+1 => next (digits n)
noncomputable def family (n : Nat) : Z0 := A [] (enc (digits n))
noncomputable def cost (n : Nat) : Nat := epochCost (digits n)

theorem entry : run0 table 14 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem cost_pos (n : Nat) : 0 < cost n := (epoch (digits n)).choose_spec.choose_spec.1

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) :=
  (epoch (digits n)).choose_spec.choose_spec.2

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 14 cost entry cost_pos growth m hm

#print axioms epoch
#print axioms growth
#print axioms never
end BB6.Agent10Raw107LF180
