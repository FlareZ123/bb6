import ReturnInvariant
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw123.R8146
open BB6Coverage BB6Coverage.Agent31Pump
-- 1RB0LF_1RC---_0RD0RE_1LD1RE_0RB0RF_0LA1LF
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
abbrev O : List Bool := [true,true]
abbrev M : List Bool := [false,false,true,false,false,true,true,false,false,true]
abbrev T : List Bool := [true,false,true,true,false,true,false,false,true,false,false,true]
def enc : List Bool → List Bool
  | [] => []
  | b::ds => false::false::false::b::enc ds
def inc : List Bool → List Bool
  | [] => [true]
  | false::ds => true::ds
  | true::ds => false::inc ds

theorem scan (k : Nat) (L R : List Bool) :
    run0 table (6*k) ⟨0,false::L,false::true::(rep O k++R)⟩ =
      some ⟨0,false::(rep O k++L),false::true::R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    have h1 : run0 table 6 ⟨0,false::L,false::true::(rep O (k+1)++R)⟩ =
      some ⟨0,false::true::true::L,false::true::(rep O k++R)⟩ := by rfl
    have h2 := ih (true::true::L)
    have H := join0 h1 h2
    change run0 table (6+6*k) _ = some ⟨0,false::(rep O k++(O++L)),false::true::R⟩ at H
    rw [← List.append_assoc,rep_snoc O k,show 6+6*k=6*(k+1) by omega] at H
    exact H

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

theorem copy (k : Nat) (L R : List Bool) :
    run0 table (2*k) ⟨5,rep O k++L,R⟩ = some ⟨5,L,rep O k++R⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h1 : run0 table 2 ⟨5,rep O (k+1)++L,R⟩ = some ⟨5,rep O k++L,O++R⟩ := by rfl
    have H := join0 h1 (ih (O++R))
    rw [← List.append_assoc,rep_snoc O k,show 2+2*k=2*(k+1) by omega] at H
    exact H

def a (n : Nat) (ds : List Bool) : Z0 := ⟨0,[],false::true::(rep O (n+1)++M++enc ds)⟩
theorem returns (n : Nat) (ds : List Bool) : ∃ t, 0<t ∧ run0 table t (a n ds) = some (a (n+1) (inc ds)) := by
  have h1 : run0 table 6 (a n ds) = some ⟨0,false::O,false::true::(rep O n++M++enc ds)⟩ := by rfl
  have h2 := scan n O (M++enc ds)
  rw [← List.append_assoc] at h2
  have h3 : run0 table 14 ⟨0,false::(rep O n++O),false::true::(M++enc ds)⟩ =
    some ⟨3,T++true::(rep O n++O),enc ds⟩ := by rfl
  obtain ⟨t,ht,h4⟩ := carry ds (T.tail++true::(rep O n++O))
  have h5 : run0 table 50 ⟨0,T++true::(rep O n++O),enc (inc ds)⟩ =
    some ⟨5,true::(rep O n++O),O++M++enc (inc ds)⟩ := by rfl
  have h6 := copy (n+1) [true] (O++M++enc (inc ds))
  have hl (k : Nat) : true::(rep O k++O) = rep O (k+1)++[true] := by
    induction k with
    | zero => rfl
    | succ k ih =>
      change true::true::(true::(rep O k++O)) = true::true::(rep O (k+1)++[true])
      rw [ih]
  rw [hl n] at h3 h4 h5
  have h7 : run0 table 2 ⟨5,[true],rep O (n+1)++(O++M++enc (inc ds))⟩ = some (a (n+1) (inc ds)) := by
    change some (⟨0,[],false::true::(rep O (n+1)++(O++M++enc (inc ds)))⟩ : Z0) = _
    simp only [a,← List.append_assoc,rep_snoc O (n+1)]
    rfl
  have H := join0 (join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4) h5) h6) h7
  exact ⟨_,by omega,H⟩
theorem entry : run0 table 74 ⟨0,[],[]⟩ = some (a 0 []) := by rfl
inductive Inv : Z0 → Prop
  | mk (n : Nat) (ds : List Bool) : Inv (a n ds)
theorem progress (c : Z0) (h : Inv c) : ∃ t d, 0<t ∧ run0 table t c = some d ∧ Inv d := by
  cases h with
  | mk n ds =>
    obtain ⟨t,ht,h⟩ := returns n ds
    exact ⟨t,_,ht,h,.mk (n+1) (inc ds)⟩
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_return table Inv 74 (a 0 []) entry (.mk 0 []) progress m hm
#print axioms never
end BB6.Agent25Raw123.R8146
