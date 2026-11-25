import ReturnInvariant
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw123.R8209
open BB6Coverage BB6Coverage.Agent31Pump
-- 1RB0LF_1RC---_0RD1RE_1LD1RE_0RB0RF_0LA1LF
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
def enc : List Bool → List Bool
  | [] => []
  | b::ds => false::false::false::b::enc ds
def inc : List Bool → List Bool
  | [] => [true]
  | false::ds => true::ds
  | true::ds => false::inc ds

theorem carry (ds L : List Bool) : ∃ t, 0<t ∧
    run0 table t ⟨3,true::L,enc ds⟩ = some ⟨0,true::L,enc (inc ds)⟩ := by
  induction ds generalizing L with
  | nil => exact ⟨12,by decide,by rfl⟩
  | cons b ds ih =>
    cases b with
    | false => exact ⟨12,by decide,by rfl⟩
    | true =>
      have h1 : run0 table 4 ⟨3,true::L,enc (true::ds)⟩ =
        some ⟨3,true::false::true::false::true::L,enc ds⟩ := by rfl
      obtain ⟨t,ht,h2⟩ := ih (false::true::false::true::L)
      have h3 : run0 table 4 ⟨0,true::false::true::false::true::L,enc (inc ds)⟩ =
        some ⟨0,true::L,enc (inc (true::ds))⟩ := by rfl
      exact ⟨4+t+4,by omega,join0 (join0 h1 h2) h3⟩

inductive Tail where
  | empty
  | bits (b : Bool) (ds : List Bool)
def tailWord : Tail → List Bool
  | .empty => []
  | .bits b ds => false::false::b::enc ds
def nextTail : Tail → Tail
  | .empty => .bits true []
  | .bits false ds => .bits true ds
  | .bits true ds => .bits false (inc ds)
def rest (b : Bool) (tail : Tail) : List Bool := false::b::false::false::false::true::true::tailWord tail
def nextRest (b : Bool) (tail : Tail) : Tail := if b then nextTail tail else tail

theorem secondary (tail : Tail) (L : List Bool) : ∃ t, 0<t ∧
    run0 table t ⟨3,true::L,true::tailWord tail⟩ =
      some ⟨0,true::true::true::L,(tailWord (nextTail tail)).tail⟩ := by
  cases tail with
  | empty => exact ⟨12,by decide,by rfl⟩
  | bits b ds =>
    cases b with
    | false => exact ⟨12,by decide,by rfl⟩
    | true =>
      have h1 : run0 table 6 ⟨3,true::L,true::tailWord (.bits true ds)⟩ =
        some ⟨3,true::false::true::true::true::L,enc ds⟩ := by rfl
      obtain ⟨t,ht,h2⟩ := carry ds (false::true::true::true::L)
      have h3 : run0 table 2 ⟨0,true::false::true::true::true::L,enc (inc ds)⟩ =
        some ⟨0,true::true::true::L,(tailWord (nextTail (.bits true ds))).tail⟩ := by rfl
      exact ⟨6+t+2,by omega,join0 (join0 h1 h2) h3⟩

theorem marker (b : Bool) (tail : Tail) (L : List Bool) : ∃ t, 0<t ∧
    run0 table t ⟨3,true::L,true::false::rest b tail⟩ =
      some ⟨0,true::true::true::L,rest (!b) (nextRest b tail)⟩ := by
  cases b with
  | false => exact ⟨12,by decide,by rfl⟩
  | true =>
    have h1 : run0 table 6 ⟨3,true::L,true::false::rest true tail⟩ =
      some ⟨3,true::false::true::true::true::L,false::false::false::true::true::tailWord tail⟩ := by rfl
    have h2 : run0 table 4 ⟨3,true::false::true::true::true::L,false::false::false::true::true::tailWord tail⟩ =
      some ⟨3,true::false::true::false::true::false::true::true::true::L,true::tailWord tail⟩ := by rfl
    obtain ⟨t,ht,h3⟩ := secondary tail (false::true::false::true::false::true::true::true::L)
    let R := (tailWord (nextTail tail)).tail
    have h4 : run0 table 4 ⟨0,true::true::true::false::true::false::true::false::true::true::true::L,R⟩ =
      some ⟨0,true::false::true::false::true::true::true::L,false::true::true::false::R⟩ := by rfl
    have h5 : run0 table 4 ⟨0,true::false::true::false::true::true::true::L,false::true::true::false::R⟩ =
      some ⟨0,true::true::true::L,rest (!true) (nextRest true tail)⟩ := by
      cases tail with
      | empty => rfl
      | bits b ds => cases b <;> rfl
    exact ⟨_,by omega,join0 (join0 (join0 (join0 h1 h2) h3) h4) h5⟩

abbrev P : List Bool := [true,false,false,true]
abbrev Q : List Bool := [false,true,true,false]
abbrev B : List Bool := [false,false,true,true]
theorem sweep (k : Nat) (b : Bool) (tail : Tail) (L : List Bool) : ∃ t, 0<t ∧
    run0 table t ⟨3,true::L,rep P k++true::false::rest b tail⟩ =
      some ⟨0,true::true::true::L,rep Q k++rest (!b) (nextRest b tail)⟩ := by
  induction k generalizing L with
  | zero => exact marker b tail L
  | succ k ih =>
    have h1 : run0 table 6 ⟨3,true::L,rep P (k+1)++true::false::rest b tail⟩ =
      some ⟨3,true::false::true::true::true::L,rep P k++true::false::rest b tail⟩ := by rfl
    obtain ⟨t,ht,h2⟩ := ih (false::true::true::true::L)
    have h3 : run0 table 4 ⟨0,true::true::true::false::true::true::true::L,rep Q k++rest (!b) (nextRest b tail)⟩ =
      some ⟨0,true::true::true::L,rep Q (k+1)++rest (!b) (nextRest b tail)⟩ := by rfl
    exact ⟨6+t+4,by omega,join0 (join0 h1 h2) h3⟩

theorem bridgeP (k : Nat) (R : List Bool) : true::(rep B k++false::false::R) = rep P k++true::false::false::R := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change true::false::false::true::(true::(rep B k++false::false::R)) = true::false::false::true::(rep P k++true::false::false::R)
    rw [ih]
theorem bridgeQ (k : Nat) (R : List Bool) : false::(rep Q k++false::R) = rep B k++false::false::R := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change false::false::true::true::(false::(rep Q k++false::R)) = false::false::true::true::(rep B k++false::false::R)
    rw [ih]

def a (n : Nat) (b : Bool) (tail : Tail) : Z0 := ⟨0,[],false::true::true::(rep B (n+1)++false::rest b tail)⟩
theorem returns (n : Nat) (b : Bool) (tail : Tail) : ∃ t, 0<t ∧
    run0 table t (a n b tail) = some (a (n+1) (!b) (nextRest b tail)) := by
  have h1 : run0 table 8 (a n b tail) =
    some ⟨3,[true,false,true,true,true,true,true],true::(rep B n++false::rest b tail)⟩ := by rfl
  rw [rest,bridgeP] at h1
  obtain ⟨t,ht,h2⟩ := sweep n b tail [false,true,true,true,true,true]
  have h3 : run0 table 4 ⟨0,[true,true,true,false,true,true,true,true,true],rep Q n++rest (!b) (nextRest b tail)⟩ =
    some ⟨0,[true,true,true,true,true],rep Q (n+1)++rest (!b) (nextRest b tail)⟩ := by rfl
  have h4 : run0 table 6 ⟨0,[true,true,true,true,true],rep Q (n+1)++rest (!b) (nextRest b tail)⟩ =
    some ⟨0,[],false::true::true::true::true::false::(rep Q (n+1)++rest (!b) (nextRest b tail))⟩ := by rfl
  rw [rest,bridgeQ] at h4
  have h5 : run0 table 10 ⟨0,[],false::true::true::true::true::(rep B (n+1)++false::rest (!b) (nextRest b tail))⟩ =
    some (a (n+1) (!b) (nextRest b tail)) := by rfl
  exact ⟨_,by omega,join0 (join0 (join0 (join0 h1 h2) h3) h4) h5⟩
theorem entry : run0 table 74 ⟨0,[],[]⟩ = some (a 0 false .empty) := by rfl
inductive Inv : Z0 → Prop
  | mk (n : Nat) (b : Bool) (tail : Tail) : Inv (a n b tail)
theorem progress (c : Z0) (h : Inv c) : ∃ t d, 0<t ∧ run0 table t c = some d ∧ Inv d := by
  cases h with
  | mk n b tail =>
    obtain ⟨t,ht,h⟩ := returns n b tail
    exact ⟨t,_,ht,h,.mk (n+1) (!b) (nextRest b tail)⟩
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_return table Inv 74 (a 0 false .empty) entry (.mk 0 false .empty) progress m hm
#print axioms never
end BB6.Agent25Raw123.R8209
