import Raw58Live
namespace BB6Coverage.Agent1Raw57LD062
open BB6Coverage Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- Raw57 A1=0LD, open leaf 62. Agent 7.
def table : PartialMachine
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨false,false,3⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨false,true,2⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => some (some ⟨false,false,5⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨true,true,4⟩)
  | (4,false) => some (some ⟨false,true,1⟩)
  | (4,true) => some (some ⟨false,false,0⟩)
  | (5,false) => none
  | (5,true) => some (some ⟨true,false,0⟩)
  | _ => none
abbrev U : List Bool := [true,false,false,false]
abbrev Z : List Bool := [false,false,false,false]
abbrev V : List Bool := [true,false,true,false]
abbrev Q : List Bool := [false,false,true]
abbrev S : List Bool := [false,true,true]
def D (R : List Bool) : Z0 := ⟨3,[true],Q++R⟩

theorem enterCounter (R : List Bool) :
    run0 table 7 (D R) = some ⟨2,false::S,R⟩ := by rfl

theorem rightCarry (n : Nat) (L R : List Bool) :
    run0 table (4*n) ⟨2,false::L,rep U n++R⟩ = some ⟨2,false::(rep V n++L),R⟩ := by
  exact sweepR table 2 [false] [] U V 4 (by intro L R; rfl) n L R

theorem leftReset (n : Nat) (L R : List Bool) :
    run0 table (8*n) ⟨3,false::(rep V n++L),R⟩ = some ⟨3,false::L,rep Z n++R⟩ := by
  exact sweepL table 3 [false] [] V Z 8 (by intro L R; rfl) n L R

theorem carry (k : Nat) (R : List Bool) :
    run0 table (14+12*k) (D (rep U k++Z++R)) = some (D (rep Z k++U++R)) := by
  cases k with
  | zero => rfl
  | succ n =>
    have h1 := enterCounter (rep U (n+1)++(Z++R))
    have h2 := rightCarry (n+1) S (Z++R)
    have h3 : run0 table 1 ⟨2,false::(rep V (n+1)++S),Z++R⟩ =
      some ⟨3,false::false::(rep V (n+1)++S),[false,false,false]++R⟩ := by rfl
    have h4 : run0 table 9 ⟨3,false::false::(rep V (n+1)++S),[false,false,false]++R⟩ =
      some ⟨3,false::(rep V n++S),Z++U++R⟩ := by rfl
    have h5 := leftReset n S (Z++U++R)
    have h6 : run0 table 5 ⟨3,false::S,rep Z n++(Z++U++R)⟩ =
      some (D (rep Z n++(Z++U++R))) := by rfl
    have h := join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4) h5) h6
    rw [show 7+4*(n+1)+1+9+8*n+5=14+12*(n+1) by omega] at h
    simpa only [List.append_assoc,← List.append_assoc (rep Z n) Z (U++R),rep_snoc,rep] using h

theorem overflow (k : Nat) :
    run0 table (26+12*k) (D (rep U k++[true])) = some (D (rep Z (k+1)++[true])) := by
  have h1 := enterCounter (rep U k++[true])
  have h2 := rightCarry k S [true]
  have h3 : run0 table 5 ⟨2,false::(rep V k++S),[true]⟩ =
    some ⟨3,false::false::(V++rep V k++S),[]⟩ := by rfl
  have h4 : run0 table 9 ⟨3,false::false::(V++rep V k++S),[]⟩ =
    some ⟨3,false::(rep V k++S),Z++[true]⟩ := by rfl
  have h5 := leftReset k S (Z++[true])
  have h6 : run0 table 5 ⟨3,false::S,rep Z k++(Z++[true])⟩ =
    some (D (rep Z k++(Z++[true]))) := by rfl
  have h := join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4) h5) h6
  rw [show 7+4*k+5+9+8*k+5=26+12*k by omega] at h
  simpa only [List.append_assoc,← List.append_assoc (rep Z k) Z [true],rep_snoc,rep] using h

def enc : List Bool → List Bool
  | [] => []
  | b::bs => (if b then U else Z) ++ enc bs

theorem enc_append (a b : List Bool) : enc (a++b) = enc a++enc b := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append,enc,ih,List.append_assoc]
theorem enc_zeroes (n : Nat) : enc (rep [false] n) = rep Z n := by
  induction n with
  | zero => rfl
  | succ n ih => change Z ++ enc (rep [false] n) = Z ++ rep Z n; rw [ih]

theorem progressAux (ds : List Bool) (k : Nat) :
    ∃ t ds', 0<t ∧ run0 table t (D (rep U k++enc ds++[true])) = some (D (enc ds'++[true])) := by
  induction ds generalizing k with
  | nil =>
    refine ⟨26+12*k,rep [false] (k+1),by omega,?_⟩
    simpa only [enc,List.append_nil,enc_zeroes] using overflow k
  | cons b bs ih =>
    cases b with
    | false =>
      refine ⟨14+12*k,rep [false] k++true::bs,by omega,?_⟩
      simpa only [enc_append,enc_zeroes,enc,ite_false,ite_true,Bool.false_eq_true,List.append_assoc] using carry k (enc bs++[true])
    | true =>
      obtain ⟨t,ds',hp,h⟩ := ih (k+1)
      refine ⟨t,ds',hp,?_⟩
      simpa only [enc,ite_true,← List.append_assoc,rep_snoc U k,rep] using h

theorem progress (ds : List Bool) :
    ∃ t ds', 0<t ∧ run0 table t (D (enc ds++[true])) = some (D (enc ds'++[true])) := by
  simpa only [rep,List.nil_append] using progressAux ds 0

theorem entry : run0 table 22 ⟨0,[],[]⟩ = some (D (enc []++[true])) := by rfl

theorem arbitrary (n : Nat) : ∃ t ds, n ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some (D (enc ds++[true])) := by
  induction n with
  | zero => exact ⟨22,[],by omega,entry⟩
  | succ n ih =>
    obtain ⟨t,ds,hle,h⟩ := ih
    obtain ⟨u,ds',hp,hu⟩ := progress ds
    exact ⟨t+u,ds',by omega,join0 h hu⟩
#print axioms carry
#print axioms overflow
#print axioms entry
#print axioms arbitrary

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply Agent4Live.never_of_live table _ m hm
  intro n
  obtain ⟨t,ds,hle,h⟩ := arbitrary n
  exact ⟨t,D (enc ds++[true]),hle,h⟩
#print axioms never
end BB6Coverage.Agent1Raw57LD062
