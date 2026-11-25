import Raw58Live
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent7LFGrowth
open BB6Coverage Agent31Pump

-- false = LF411, true = LF415.
def table (v : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (if v then some ⟨true,false,3⟩ else some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

def P : List Bool := [true,false]
def Q : List Bool := [false,true]
def good (n : Nat) : Z0 := ⟨2,false::(rep P n ++ [true]),[]⟩
def bad (a b : Nat) : Z0 := ⟨2,false::(rep P a ++ [true,true] ++ rep Q b),[]⟩
def bt (v : Bool) : Nat := if v then 4 else 2

theorem rot (n : Nat) : true::rep Q n = rep P n ++ [true] := by
  simpa only [P,Q,List.singleton_append] using rotate true [false] n

theorem goodQ (n : Nat) : good n = ⟨2,rep Q (n+1),[]⟩ := by
  unfold good
  rw [← rot]
  rfl

theorem goodInit (v : Bool) (n : Nat) :
    run0 (table v) 5 (good n) = some ⟨0,rep P (n+1) ++ [true],[]⟩ := by
  cases n <;> cases v <;> rfl

theorem badInit (v : Bool) (a b : Nat) :
    run0 (table v) 5 (bad a b) = some ⟨0,rep P (a+1) ++ [true,true] ++ rep Q b,[]⟩ := by
  cases a <;> cases v <;> rfl

theorem asweep (v : Bool) (n : Nat) (L R : List Bool) :
    run0 (table v) (2*n) ⟨0,rep P n++L,R⟩ = some ⟨0,L,rep P n++R⟩ := by
  simpa only [List.nil_append] using sweepL (table v) 0 [] [] P P 2
    (by intro L R; cases v <;> rfl) n L R

theorem aright (v : Bool) (n : Nat) (L R : List Bool) :
    run0 (table v) (bt v*n) ⟨0,false::L,rep P n++R⟩ = some ⟨0,false::(rep Q n++L),R⟩ := by
  simpa only [List.singleton_append,List.nil_append,List.append_assoc,List.cons_append] using
    sweepR (table v) 0 [false] [] P Q (bt v) (by intro L R; cases v <;> rfl) n L R

theorem bright (v : Bool) (n : Nat) (L R : List Bool) :
    run0 (table v) (2*n) ⟨1,false::L,rep P n++R⟩ = some ⟨1,false::(rep Q n++L),R⟩ := by
  simpa only [List.singleton_append,List.nil_append,List.append_assoc,List.cons_append] using
    sweepR (table v) 1 [false] [] P Q 2 (by intro L R; cases v <;> rfl) n L R

theorem goodToBad (v : Bool) (n : Nat) : ∃ t, 0<t ∧
    run0 (table v) t (good n) = some (bad 0 (n+2)) := by
  have h1 := goodInit v n
  have h2 := asweep v (n+1) [true] []
  have h3 : run0 (table v) 2 ⟨0,[true],rep P (n+1)⟩ = some ⟨0,[],rep P (n+2)⟩ := by cases v <;> rfl
  have h4 : run0 (table v) (bt v) ⟨0,[],rep P (n+2)⟩ = some ⟨0,[false,false,true],rep P (n+1)⟩ := by cases v <;> rfl
  have h5 := aright v (n+1) [false,true] []
  have h6 : run0 (table v) 2 ⟨0,false::(rep Q (n+1)++[false,true]),[]⟩ = some (bad 0 (n+2)) := by
    change run0 (table v) 2 ⟨0,false::(rep Q (n+1)++Q),[]⟩ = some (bad 0 (n+2))
    rw [rep_snoc Q (n+1)]
    cases v <;> rfl
  simp only [List.append_nil] at h2 h5
  exact ⟨_,by omega,join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4) h5) h6⟩

theorem badToB (v : Bool) (a b : Nat) : ∃ t, 0<t ∧
    run0 (table v) t (bad a b) = some ⟨1,rep Q b,rep P (a+2)⟩ := by
  have h1 := badInit v a b
  have h2 := asweep v (a+1) ([true,true]++rep Q b) []
  have h3 : run0 (table v) 2 ⟨0,[true,true]++rep Q b,rep P (a+1)⟩ = some ⟨1,rep Q b,rep P (a+2)⟩ := by cases v <;> rfl
  simp only [List.append_assoc] at h1
  simp only [List.append_nil] at h2
  exact ⟨_,by omega,join0 (join0 h1 h2) h3⟩

theorem badStep (v : Bool) (a b : Nat) : ∃ t, 0<t ∧
    run0 (table v) t (bad a (b+1)) = some (bad (a+2) b) := by
  obtain ⟨t,ht,h1⟩ := badToB v a (b+1)
  have h2 := bright v (a+2) (true::rep Q b) []
  have h3 : run0 (table v) 1 ⟨1,false::(rep Q (a+2)++true::rep Q b),[]⟩ = some (bad (a+2) b) := by
    have he : true::(rep Q (a+2)++true::rep Q b) = rep P (a+2)++[true,true]++rep Q b := by
      rw [← List.cons_append,rot]
      simp only [List.append_assoc,List.singleton_append]
      rfl
    have hh : run0 (table v) 1 ⟨1,false::(rep Q (a+2)++true::rep Q b),[]⟩ =
        some ⟨2,false::true::(rep Q (a+2)++true::rep Q b),[]⟩ := by cases v <;> rfl
    rw [he] at hh
    exact hh
  simp only [List.append_nil] at h2
  exact ⟨_,by omega,join0 (join0 h1 h2) h3⟩

theorem badEnd (v : Bool) (a : Nat) : ∃ t, 0<t ∧
    run0 (table v) t (bad a 0) = some (good (a+2)) := by
  obtain ⟨t,ht,h1⟩ := badToB v a 0
  have h2 : run0 (table v) 2 ⟨1,[],rep P (a+2)⟩ = some ⟨1,[false,false,true],rep P (a+1)⟩ := by cases v <;> rfl
  have h3 := bright v (a+1) [false,true] []
  have h4 : run0 (table v) 1 ⟨1,false::(rep Q (a+1)++[false,true]),[]⟩ = some (good (a+2)) := by
    change run0 (table v) 1 ⟨1,false::(rep Q (a+1)++Q),[]⟩ = some (good (a+2))
    rw [rep_snoc Q (a+1),goodQ]
    cases v <;> rfl
  simp only [List.append_nil] at h3
  exact ⟨_,by omega,join0 (join0 (join0 h1 h2) h3) h4⟩

theorem badResolve (v : Bool) (a b : Nat) : ∃ t, 0<t ∧
    run0 (table v) t (bad a b) = some (good (a+2*b+2)) := by
  induction b generalizing a with
  | zero => simpa using badEnd v a
  | succ b ih =>
    obtain ⟨t,ht,h1⟩ := badStep v a b
    obtain ⟨u,hu,h2⟩ := ih (a+2)
    have h := join0 h1 h2
    rw [show a+2+2*b+2=a+2*(b+1)+2 by omega] at h
    exact ⟨_,by omega,h⟩

theorem grow (v : Bool) (n : Nat) : ∃ t, 0<t ∧
    run0 (table v) t (good n) = some (good (2*n+6)) := by
  obtain ⟨t,ht,h1⟩ := goodToBad v n
  obtain ⟨u,hu,h2⟩ := badResolve v 0 (n+2)
  have h := join0 h1 h2
  rw [show 0+2*(n+2)+2=2*n+6 by omega] at h
  exact ⟨_,by omega,h⟩

theorem arbitrary (v : Bool) (n : Nat) : ∃ t z, n ≤ t ∧ run0 (table v) t ⟨0,[],[]⟩ = some z := by
  have aux : ∀ k : Nat, ∃ t j, k ≤ t ∧ run0 (table v) t ⟨0,[],[]⟩ = some (good j) := by
    intro k
    induction k with
    | zero => exact ⟨16,2,by omega,by cases v <;> rfl⟩
    | succ k ih =>
      obtain ⟨t,j,ht,h1⟩ := ih
      obtain ⟨u,hu,h2⟩ := grow v j
      exact ⟨_,_,by omega,join0 h1 h2⟩
  obtain ⟨t,j,ht,h⟩ := aux n
  exact ⟨t,good j,ht,h⟩

theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  Agent4Live.never_of_live (table v) (arbitrary v) m hm

#print axioms arbitrary
#print axioms never
end BB6Coverage.Agent7LFGrowth

namespace BB6Coverage.Agent7LF411
def table := Agent7LFGrowth.table false
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent7LFGrowth.never false m hm
end BB6Coverage.Agent7LF411

namespace BB6Coverage.Agent7LF415
def table := Agent7LFGrowth.table true
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent7LFGrowth.never true m hm
end BB6Coverage.Agent7LF415
