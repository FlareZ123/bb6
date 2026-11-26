import Raw58Live
namespace BB6Coverage.Agent7Raw57LB1Counters
open BB6Coverage Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0
inductive Variant where | a | b | c | d
open Variant

def table (v : Variant) : PartialMachine
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨true,false,1⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => match v with
    | a => some (some ⟨false,true,4⟩)
    | b | c => some (some ⟨false,true,5⟩)
    | d => some (some ⟨true,true,5⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => match v with
    | c => some (some ⟨false,false,5⟩)
    | _ => some (some ⟨false,false,4⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨true,true,4⟩)
  | (4,false) => match v with
    | a => some (some ⟨false,true,5⟩)
    | _ => some (some ⟨false,true,1⟩)
  | (4,true) => some (some ⟨false,false,0⟩)
  | (5,false) => match v with
    | a => some (some ⟨true,true,2⟩)
    | _ => none
  | (5,true) => match v with
    | a => none
    | d => some (some ⟨true,true,2⟩)
    | _ => some (some ⟨false,false,0⟩)
  | _ => none
abbrev U : List Bool := [true,false,false,false]
abbrev Z : List Bool := [false,false,false,false]
abbrev V : List Bool := [true,false,true,false]
abbrev J : List Bool := [false,true,false,true]
abbrev Q : List Bool := [true,false]
abbrev S : List Bool := [true,true]
def B (R : List Bool) : Z0 := ⟨1,[true],Q++R⟩
def prefCost : Variant → Nat | d => 2 | _ => 4

theorem enterCounter (v : Variant) (R : List Bool) :
    run0 (table v) (prefCost v) (B R) = some ⟨2,false::S,R⟩ := by cases v <;> rfl

theorem rightCarry (v : Variant) (n : Nat) (L R : List Bool) :
    run0 (table v) (4*n) ⟨2,false::L,rep U n++R⟩ = some ⟨2,false::(rep V n++L),R⟩ := by
  exact sweepR (table v) 2 [false] [] U V 4 (by intro L R; cases v <;> rfl) n L R

theorem leftReset (v : Variant) (n : Nat) (L R : List Bool) :
    run0 (table v) (8*n) ⟨1,rep J n++L,Q++R⟩ = some ⟨1,L,Q++rep Z n++R⟩ := by
  exact sweepL (table v) 1 [] Q J Z 8 (by intro L R; cases v <;> rfl) n L R

theorem rotate (n : Nat) : rep V n++[true] = true::rep J n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change V ++ (rep V n++[true]) = true::(J++rep J n)
    rw [ih]
    rfl

theorem leftTurn (v : Variant) (n : Nat) (R : List Bool) :
    run0 (table v) 5 ⟨3,false::false::(rep V n++S),R⟩ =
    some ⟨1,rep J n++[true],[true,false,true]++R⟩ := by
  have e : rep V n++S = true::(rep J n++[true]) := by
    change rep V n++([true]++[true]) = _
    rw [← List.append_assoc,rotate]
    rfl
  rw [e]
  cases v <;> rfl

theorem carry (v : Variant) (k : Nat) (R : List Bool) :
    run0 (table v) (prefCost v+6+12*k) (B (rep U k++Z++R)) = some (B (rep Z k++U++R)) := by
  have h1 := enterCounter v (rep U k++(Z++R))
  have h2 := rightCarry v k S (Z++R)
  have h3 : run0 (table v) 1 ⟨2,false::(rep V k++S),Z++R⟩ =
    some ⟨3,false::false::(rep V k++S),[false,false,false]++R⟩ := by cases v <;> rfl
  have h4 := leftTurn v k ([false,false,false]++R)
  have h5 := leftReset v k [true] (U++R)
  have h := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  rw [show prefCost v+4*k+1+5+8*k=prefCost v+6+12*k by omega] at h
  simpa only [B,List.append_assoc] using h

theorem overflow (v : Variant) (k : Nat) :
    run0 (table v) (prefCost v+18+12*k) (B (rep U k++[true])) = some (B (rep Z (k+1)++[true])) := by
  have h1 := enterCounter v (rep U k++[true])
  have h2 := rightCarry v k S [true]
  have h3 : run0 (table v) 5 ⟨2,false::(rep V k++S),[true]⟩ =
    some ⟨3,false::false::(rep V (k+1)++S),[]⟩ := by cases v <;> rfl
  have h4 := leftTurn v (k+1) []
  have h5 := leftReset v (k+1) [true] [true]
  have h := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  rw [show prefCost v+4*k+5+5+8*(k+1)=prefCost v+18+12*k by omega] at h
  exact h

def enc : List Bool → List Bool
  | [] => []
  | bit::bs => (if bit then U else Z) ++ enc bs

theorem enc_append (a b : List Bool) : enc (a++b) = enc a++enc b := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append,enc,ih,List.append_assoc]
theorem enc_zeroes (n : Nat) : enc (rep [false] n) = rep Z n := by
  induction n with
  | zero => rfl
  | succ n ih => change Z ++ enc (rep [false] n) = Z ++ rep Z n; rw [ih]

theorem progressAux (v : Variant) (ds : List Bool) (k : Nat) :
    ∃ t ds', 0<t ∧ run0 (table v) t (B (rep U k++enc ds++[true])) = some (B (enc ds'++[true])) := by
  induction ds generalizing k with
  | nil =>
    refine ⟨prefCost v+18+12*k,rep [false] (k+1),by omega,?_⟩
    simpa only [enc,List.append_nil,enc_zeroes] using overflow v k
  | cons b bs ih =>
    cases b with
    | false =>
      refine ⟨prefCost v+6+12*k,rep [false] k++true::bs,by omega,?_⟩
      simpa only [enc_append,enc_zeroes,enc,ite_false,ite_true,Bool.false_eq_true,List.append_assoc] using carry v k (enc bs++[true])
    | true =>
      obtain ⟨t,ds',hp,h⟩ := ih (k+1)
      refine ⟨t,ds',hp,?_⟩
      simpa only [enc,ite_true,← List.append_assoc,rep_snoc U k,rep] using h

theorem progress (v : Variant) (ds : List Bool) :
    ∃ t ds', 0<t ∧ run0 (table v) t (B (enc ds++[true])) = some (B (enc ds'++[true])) := by
  simpa only [rep,List.nil_append] using progressAux v ds 0

def entryCost : Variant → Nat | d => 28 | _ => 30
theorem entry (v : Variant) : run0 (table v) (entryCost v) ⟨0,[],[]⟩ = some (B (enc [false]++[true])) := by cases v <;> rfl

theorem arbitrary (v : Variant) (n : Nat) : ∃ t ds, n ≤ t ∧ run0 (table v) t ⟨0,[],[]⟩ = some (B (enc ds++[true])) := by
  induction n with
  | zero => exact ⟨entryCost v,[false],by omega,entry v⟩
  | succ n ih =>
    obtain ⟨t,ds,hle,h⟩ := ih
    obtain ⟨u,ds',hp,hu⟩ := progress v ds
    exact ⟨t+u,ds',by omega,join0 h hu⟩
#print axioms carry
#print axioms overflow
#print axioms entry
#print axioms arbitrary

theorem never (v : Variant) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  apply Agent4Live.never_of_live (table v) _ m hm
  intro n
  obtain ⟨t,ds,hle,h⟩ := arbitrary v n
  exact ⟨t,B (enc ds++[true]),hle,h⟩
#print axioms never
namespace M398
abbrev table := Agent7Raw57LB1Counters.table .a
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent7Raw57LB1Counters.never .a m hm
end M398
namespace M401
abbrev table := Agent7Raw57LB1Counters.table .b
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent7Raw57LB1Counters.never .b m hm
end M401
namespace M402
abbrev table := Agent7Raw57LB1Counters.table .c
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent7Raw57LB1Counters.never .c m hm
end M402
namespace M1256
abbrev table := Agent7Raw57LB1Counters.table .d
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent7Raw57LB1Counters.never .d m hm
end M1256
end BB6Coverage.Agent7Raw57LB1Counters
