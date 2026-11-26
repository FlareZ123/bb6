import Raw58Live
namespace BB6Coverage.Agent7Raw58RD8
open BB6Coverage Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def table : PartialMachine
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨false,true,3⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨true,true,3⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => none
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨true,true,4⟩)
  | (4,false) => some (some ⟨false,false,5⟩)
  | (4,true) => some (some ⟨false,true,0⟩)
  | (5,false) => some (some ⟨true,false,0⟩)
  | (5,true) => some (some ⟨true,false,5⟩)
  | _ => none
abbrev U : List Bool := [true,true,true]
abbrev Z : List Bool := [true,false,false]
def E (L : List Bool) : Z0 := ⟨4,false::L,[]⟩

theorem onesLeft (n : Nat) (L R : List Bool) :
    run0 table (3*n) ⟨5,rep U n++L,R⟩ = some ⟨5,L,rep U n++R⟩ := by
  exact sweepL table 5 [] [] U U 3 (by intro L R; rfl) n L R

theorem resetRight (n : Nat) (L R : List Bool) :
    run0 table (3*n) ⟨4,true::(L),rep U n++R⟩ = some ⟨4,true::(rep Z n++L),R⟩ := by
  exact sweepR table 4 [true] [] U Z 3 (by intro L R; rfl) n L R

theorem twoOnes (n : Nat) : [true,true] ++ rep U n = rep U n ++ [true,true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rep,List.append_assoc]
    change true::true::true::([true,true] ++ rep U n) = true::true::true::(rep U n ++ [true,true])
    rw [ih]

theorem oneOne (n : Nat) : [true] ++ rep U n = rep U n ++ [true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rep,List.append_assoc]
    change true::true::true::([true] ++ rep U n) = true::true::true::(rep U n ++ [true])
    rw [ih]

theorem carry (k : Nat) (R : List Bool) :
    run0 table (6*(k+1)) (E (rep U k++Z++R)) = some (E (rep Z k++U++R)) := by
  cases k with
  | zero => rfl
  | succ n =>
    have h1 : run0 table 1 (E (rep U (n+1)++(Z++R))) = some ⟨5,rep U (n+1)++(Z++R),[false]⟩ := by rfl
    have h2 := onesLeft (n+1) (Z++R) [false]
    have h3 : run0 table 5 ⟨5,Z++R,rep U (n+1)++[false]⟩ = some ⟨4,true::(U++R),rep U n++[true,true,false]⟩ := by
      have eq : (rep U n++[true,true,false]) = [true,true]++(rep U n++[false]) := by
        rw [← List.append_assoc,twoOnes,List.append_assoc]; rfl
      rw [eq]; rfl
    have h4 := resetRight n (U++R) [true,true,false]
    have h5 : run0 table 3 ⟨4,true::(rep Z n++(U++R)),[true,true,false]⟩ = some (E (Z++(rep Z n++(U++R)))) := by rfl
    have h := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
    simpa [rep,List.append_assoc,show 1+3*(n+1)+5+3*n+3=6*(n+1+1) by omega] using h

theorem overflow (n : Nat) :
    run0 table (6*n+17) (E (rep U (n+1))) = some (E (rep Z (n+1)++U)) := by
  have h1 : run0 table 1 (E (rep U (n+1))) = some ⟨5,rep U (n+1),[false]⟩ := by rfl
  have h2 := onesLeft (n+1) [] [false]
  simp only [List.append_nil] at h2
  have h3 : run0 table 4 ⟨5,[],rep U (n+1)++[false]⟩ = some ⟨4,true::U,rep U n++[true,false]⟩ := by
    have eq : (rep U n++[true,false]) = [true]++(rep U n++[false]) := by
      rw [← List.append_assoc,oneOne,List.append_assoc]; rfl
    rw [eq]; rfl
  have h4 := resetRight n U [true,false]
  have h5 : run0 table 9 ⟨4,true::(rep Z n++U),[true,false]⟩ = some (E (rep Z (n+1)++U)) := by
    cases n <;> rfl
  have h := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  simpa [show 1+3*(n+1)+4+3*n+9=6*n+17 by omega] using h
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
  | succ n ih =>
    change Z ++ enc (rep [false] n) = Z ++ rep Z n
    rw [ih]

theorem progressAux (ds : List Bool) (k : Nat) :
    ∃ t ds', 0 < t ∧ run0 table t (E (rep U k++enc ds++U)) = some (E (enc ds'++U)) := by
  induction ds generalizing k with
  | nil =>
    refine ⟨6*k+17,rep [false] (k+1),by omega,?_⟩
    simp only [enc,List.append_nil,enc_zeroes]
    rw [rep_snoc U k]
    exact overflow k
  | cons b bs ih =>
    cases b with
    | false =>
      refine ⟨6*(k+1),rep [false] k++true::bs,by omega,?_⟩
      simpa only [enc_append,enc_zeroes,enc,ite_false,ite_true,Bool.false_eq_true,List.append_assoc] using carry k (enc bs++U)
    | true =>
      obtain ⟨t,ds',hp,h⟩ := ih (k+1)
      refine ⟨t,ds',hp,?_⟩
      simpa only [enc,ite_true,← List.append_assoc,rep_snoc U k,rep] using h

theorem progress (ds : List Bool) :
    ∃ t ds', 0<t ∧ run0 table t (E (enc ds++U)) = some (E (enc ds'++U)) := by
  simpa only [rep,List.nil_append] using progressAux ds 0

theorem entry : run0 table 2480 ⟨0,[],[]⟩ = some (E (enc (rep [false] 7)++U)) := by rfl

theorem arbitrary (n : Nat) : ∃ t ds, n ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some (E (enc ds++U)) := by
  induction n with
  | zero => exact ⟨2480,rep [false] 7,by omega,entry⟩
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
  exact ⟨t,E (enc ds++U),hle,h⟩
#print axioms never
end BB6Coverage.Agent7Raw58RD8
