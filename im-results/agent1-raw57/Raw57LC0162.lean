import Raw58Live
namespace BB6Coverage.Agent1Raw57LC0162
open BB6Coverage Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- Raw57 A1=0LC, open leaf 162. Agent 7.
def table : PartialMachine
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨false,false,2⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨false,false,1⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => some (some ⟨false,true,5⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨true,true,4⟩)
  | (4,false) => none
  | (4,true) => some (some ⟨false,false,0⟩)
  | (5,false) => some (some ⟨true,false,1⟩)
  | (5,true) => some (some ⟨false,true,1⟩)
  | _ => none
abbrev U : List Bool := [false,true,true]
abbrev Z : List Bool := [true,false,true]
abbrev V : List Bool := [false,true,false]
abbrev Q : List Bool := [false,false,true]
abbrev S : List Bool := [false,true,true]
abbrev Lp : List Bool := [false,false]
abbrev Rp : List Bool := [false,true]
def C (R : List Bool) : Z0 := ⟨2,[true],Q++R⟩

theorem enterCounter (R : List Bool) :
    run0 table 7 (C R) = some ⟨5,true::S,R⟩ := by rfl

theorem rightCarry (n : Nat) (L R : List Bool) :
    run0 table (3*n) ⟨5,true::(L),rep U n++R⟩ = some ⟨5,true::(rep V n++L),R⟩ := by
  exact sweepR table 5 [true] [] U V 3 (by intro L R; rfl) n L R

theorem leftReset (n : Nat) (L R : List Bool) :
    run0 table (7*n) ⟨3,Lp++rep V n++L,Rp++R⟩ = some ⟨3,Lp++L,Rp++rep Z n++R⟩ := by
  exact sweepL table 3 Lp Rp V Z 7 (by intro L R; rfl) n L R

theorem finishCounter (R : List Bool) :
    run0 table 6 ⟨3,Lp++S,Rp++R⟩ = some (C (Z++R)) := by rfl

theorem carry (k : Nat) (R : List Bool) :
    run0 table (22+10*k) (C (rep U k++Z++R)) = some (C (rep Z k++U++R)) := by
  cases k with
  | zero => rfl
  | succ n =>
    have h1 := enterCounter (rep U (n+1)++(Z++R))
    have h2 := rightCarry (n+1) S (Z++R)
    have h3 : run0 table 16 ⟨5,true::(rep V (n+1)++S),Z++R⟩ =
      some ⟨3,Lp++rep V n++S,Rp++U++R⟩ := by rfl
    have h4 := leftReset n S (U++R)
    have h5 := finishCounter (rep Z n++(U++R))
    have h := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
    rw [show 7+3*(n+1)+16+7*n+6=22+10*(n+1) by omega] at h
    simpa only [List.append_assoc,rep] using h

theorem overflow (k : Nat) :
    run0 table (22+10*k) (C (rep U k)) = some (C (rep Z (k+1))) := by
  have h1 := enterCounter (rep U k)
  have h2 := rightCarry k S []
  simp only [List.append_nil] at h2
  have h3 : run0 table 9 ⟨5,true::(rep V k++S),[]⟩ =
    some ⟨3,Lp++rep V k++S,Rp⟩ := by cases k <;> rfl
  have h4 := leftReset k S []
  simp only [List.append_nil] at h4
  have h5 := finishCounter (rep Z k)
  have h := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  rw [show 7+3*k+9+7*k+6=22+10*k by omega] at h
  simpa only [rep] using h

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
    ∃ t ds', 0<t ∧ run0 table t (C (rep U k++enc ds)) = some (C (enc ds')) := by
  induction ds generalizing k with
  | nil =>
    refine ⟨22+10*k,rep [false] (k+1),by omega,?_⟩
    simpa only [enc,List.append_nil,enc_zeroes] using overflow k
  | cons b bs ih =>
    cases b with
    | false =>
      refine ⟨22+10*k,rep [false] k++true::bs,by omega,?_⟩
      simpa only [enc_append,enc_zeroes,enc,ite_false,ite_true,Bool.false_eq_true,List.append_assoc] using carry k (enc bs)
    | true =>
      obtain ⟨t,ds',hp,h⟩ := ih (k+1)
      refine ⟨t,ds',hp,?_⟩
      simpa only [enc,ite_true,← List.append_assoc,rep_snoc U k,rep] using h

theorem progress (ds : List Bool) :
    ∃ t ds', 0<t ∧ run0 table t (C (enc ds)) = some (C (enc ds')) := by
  simpa only [rep,List.nil_append] using progressAux ds 0

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (C (enc [])) := by rfl
theorem arbitrary (n : Nat) : ∃ t ds, n ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some (C (enc ds)) := by
  induction n with
  | zero => exact ⟨8,[],by omega,entry⟩
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
  exact ⟨t,C (enc ds),hle,h⟩
#print axioms never
end BB6Coverage.Agent1Raw57LC0162
