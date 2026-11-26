import Raw58Live
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent4LF139
open BB6Coverage Agent31Pump
-- 1RB1LF_1RC---_0RD0LE_1LD1RE_0RD0RA_0LA0LB
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,3⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

def P : List Bool := [true,false]
def Q : List Bool := [false,true]
def good (n : Nat) : Z0 := ⟨3,[false,false]++rep P n++[true],[]⟩
def bad (a b : Nat) : Z0 := ⟨3,[false,false]++rep P a++[true]++rep P b++[true],[]⟩

theorem rot (n : Nat) : true::rep Q n = rep P n++[true] := by
  simpa only [P,Q,List.singleton_append] using rotate true [false] n

theorem init (n : Nat) (S : List Bool) :
    run0 table 4 ⟨3,[false,false]++rep P n++[true]++S,[]⟩ =
    some ⟨0,rep P (n+1)++[true]++S,[]⟩ := by cases n <;> rfl

theorem asweep (n : Nat) (L R : List Bool) :
    run0 table (2*n) ⟨0,rep P n++L,R⟩ = some ⟨0,L,rep Q n++R⟩ := by
  simpa only [List.nil_append] using sweepL table 0 [] [] P Q 2
    (by intro L R; rfl) n L R

theorem aright (n : Nat) (L R : List Bool) :
    run0 table (4*n) ⟨0,[false,false]++L,rep Q n++R⟩ =
    some ⟨0,[false,false]++rep P n++L,R⟩ := by
  simpa only [List.nil_append,List.append_assoc] using sweepR table 0 [false,false] [] Q P 4
    (by intro L R; rfl) n L R

theorem dright (n : Nat) (L R : List Bool) :
    run0 table (2*n) ⟨3,true::L,rep Q n++R⟩ = some ⟨3,true::(rep Q n++L),R⟩ := by
  simpa only [List.nil_append,List.singleton_append,List.cons_append,List.append_assoc] using
    sweepR table 3 [true] [] Q Q 2 (by intro L R; rfl) n L R

theorem goodToBad (n : Nat) : ∃ t, 0<t ∧
    run0 table t (good n) = some (bad 0 (n+2)) := by
  have h1 : run0 table 4 (good n) = some ⟨0,rep P (n+1)++[true],[]⟩ := by
    simpa only [good,List.append_nil] using init n []
  have h2 := asweep (n+1) [true] []
  have h3 : run0 table 2 ⟨0,[true],rep Q (n+1)⟩ = some ⟨0,[],rep Q (n+2)⟩ := by rfl
  have h4 : run0 table 4 ⟨0,[],rep Q (n+2)⟩ = some ⟨0,[false,false,true],rep Q (n+1)⟩ := by rfl
  have h5 := aright (n+1) [true] []
  have h6 : run0 table 3 ⟨0,[false,false]++rep P (n+1)++[true],[]⟩ = some (bad 0 (n+2)) := by rfl
  simp only [List.append_nil] at h2 h5
  exact ⟨_,by omega,join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4) h5) h6⟩

theorem bFinish (a : Nat) (S : List Bool) (hs : S.headD false = false) :
    run0 table (2 + 2*(a+1) + 2) ⟨1,S,rep Q (a+2)⟩ =
    some ⟨3,[false,false]++rep P (a+2)++[true]++S.tail,[]⟩ := by
  have h1 : run0 table 2 ⟨1,S,rep Q (a+2)⟩ =
      some ⟨3,true::Q++S.tail,rep Q (a+1)⟩ := by
    cases S with
    | nil => rfl
    | cons b S => cases b <;> simp_all [List.headD] <;> rfl
  have h2 := dright (a+1) (Q++S.tail) []
  have h3 : run0 table 2 ⟨3,true::(rep Q (a+1)++(Q++S.tail)),[]⟩ =
      some ⟨3,[false,false]++rep P (a+2)++[true]++S.tail,[]⟩ := by
    have h : run0 table 2 ⟨3,true::(rep Q (a+1)++(Q++S.tail)),[]⟩ =
        some ⟨3,false::false::true::(rep Q (a+1)++(Q++S.tail)),[]⟩ := by rfl
    have h' : true::(rep Q (a+1)++(Q++S.tail)) = (rep P (a+2)++[true])++S.tail := by
      rw [← List.append_assoc,rep_snoc,← List.cons_append]
      change (true::rep Q (a+2))++S.tail = _
      rw [rot]
    change run0 table 2 ⟨3,true::(rep Q (a+1)++(Q++S.tail)),[]⟩ =
      some ⟨3,false::false::((rep P (a+2)++[true])++S.tail),[]⟩
    rw [← h']
    exact h
  simp only [List.append_nil] at h2
  exact join0 (join0 h1 h2) h3

theorem badStep (a b : Nat) : ∃ t, 0<t ∧
    run0 table t (bad a (b+1)) = some (bad (a+2) b) := by
  have h1 : run0 table 4 (bad a (b+1)) = some ⟨0,rep P (a+1)++([true]++rep P (b+1)++[true]),[]⟩ := by
    simpa only [bad,List.append_assoc] using init a (rep P (b+1)++[true])
  have h2 := asweep (a+1) ([true]++rep P (b+1)++[true]) []
  have h3 : run0 table 2 ⟨0,[true]++rep P (b+1)++[true],rep Q (a+1)⟩ =
      some ⟨1,false::(rep P b++[true]),rep Q (a+2)⟩ := by rfl
  have h4 := bFinish a (false::(rep P b++[true])) rfl
  simp only [List.append_assoc,List.append_nil] at h1 h2
  exact ⟨_,by omega,join0 (join0 (join0 h1 h2) h3) (by simpa only [bad,good,List.append_assoc,List.tail_cons,List.tail_nil,List.append_nil] using h4)⟩

theorem badEnd (a : Nat) : ∃ t, 0<t ∧
    run0 table t (bad a 0) = some (good (a+2)) := by
  have h1 : run0 table 4 (bad a 0) = some ⟨0,rep P (a+1)++[true,true],[]⟩ := by
    simpa only [bad,rep,List.nil_append,List.append_assoc,List.cons_append] using init a [true]
  have h2 := asweep (a+1) [true,true] []
  have h3 : run0 table 2 ⟨0,[true,true],rep Q (a+1)⟩ = some ⟨1,[],rep Q (a+2)⟩ := by rfl
  have h4 := bFinish a [] rfl
  simp only [List.append_nil] at h2 h4
  exact ⟨_,by omega,join0 (join0 (join0 h1 h2) h3) (by simpa only [bad,good,List.append_assoc,List.tail_cons,List.tail_nil,List.append_nil] using h4)⟩

theorem badResolve (a b : Nat) : ∃ t, 0<t ∧
    run0 table t (bad a b) = some (good (a+2*b+2)) := by
  induction b generalizing a with
  | zero => simpa using badEnd a
  | succ b ih =>
    obtain ⟨t,ht,h1⟩ := badStep a b
    obtain ⟨u,hu,h2⟩ := ih (a+2)
    have h := join0 h1 h2
    rw [show a+2+2*b+2=a+2*(b+1)+2 by omega] at h
    exact ⟨_,by omega,h⟩

theorem grow (n : Nat) : ∃ t, 0<t ∧
    run0 table t (good n) = some (good (2*n+6)) := by
  obtain ⟨t,ht,h1⟩ := goodToBad n
  obtain ⟨u,hu,h2⟩ := badResolve 0 (n+2)
  have h := join0 h1 h2
  rw [show 0+2*(n+2)+2=2*n+6 by omega] at h
  exact ⟨_,by omega,h⟩

theorem arbitrary (n : Nat) : ∃ t z, n ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some z := by
  have aux : ∀ k : Nat, ∃ t j, k ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some (good j) := by
    intro k
    induction k with
    | zero => exact ⟨17,2,by omega,by rfl⟩
    | succ k ih =>
      obtain ⟨t,j,ht,h1⟩ := ih
      obtain ⟨u,hu,h2⟩ := grow j
      exact ⟨_,_,by omega,join0 h1 h2⟩
  obtain ⟨t,j,ht,h⟩ := aux n
  exact ⟨t,good j,ht,h⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table arbitrary m hm
#print axioms arbitrary
#print axioms never
end BB6Coverage.Agent4LF139
