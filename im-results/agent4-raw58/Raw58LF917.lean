import Raw58Live
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent7LF917
open BB6Coverage Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def P : List Bool := [true,false]
def Q : List Bool := [false,true]
def O : List Bool := [true,true]
def odd (a b : Nat) : Z0 := ⟨2,false::true::(rep O a++rep Q b),[]⟩
def even (a : Nat) : Z0 := ⟨2,false::rep O (a+1),[]⟩

theorem init (L : List Bool) : run0 table 10 ⟨2,false::true::L,[]⟩ = some ⟨0,L,[true,false,false]⟩ := by rfl

theorem left (a : Nat) (L R : List Bool) :
    run0 table (2*a) ⟨0,rep O a++L,R⟩ = some ⟨0,L,rep P a++R⟩ := by
  simpa only [List.nil_append] using sweepL table 0 [] [] O P 2 (by intro L R; rfl) a L R

theorem rightA (a : Nat) (L R : List Bool) :
    run0 table (2*a) ⟨0,false::L,rep P a++R⟩ = some ⟨0,false::(rep O a++L),R⟩ := by
  simpa only [List.singleton_append,List.nil_append,List.append_assoc,List.cons_append] using
    sweepR table 0 [false] [] P O 2 (by intro L R; rfl) a L R

theorem rightB (a : Nat) (L R : List Bool) :
    run0 table (2*a) ⟨1,false::L,rep P a++R⟩ = some ⟨1,false::(rep Q a++L),R⟩ := by
  simpa only [List.singleton_append,List.nil_append,List.append_assoc,List.cons_append] using
    sweepR table 1 [false] [] P Q 2 (by intro L R; rfl) a L R

theorem oddCore (a b : Nat) : run0 table (10+2*a) (odd a b) =
    some ⟨0,rep Q b,rep P (a+1)++[false]⟩ := by
  have h := join0 (init (rep O a++rep Q b)) (left a (rep Q b) [true,false,false])
  have e : rep P a++[true,false,false] = rep P (a+1)++[false] := by
    change rep P a++(P++[false]) = rep P (a+1)++[false]
    rw [← List.append_assoc,rep_snoc]
    rfl
  rw [e] at h
  exact h

theorem oddStep (a b : Nat) : ∃ t, 0<t ∧ run0 table t (odd a (b+1)) = some (odd (a+2) b) := by
  have h1 := oddCore a (b+1)
  have h2 : run0 table 2 ⟨0,rep Q (b+1),rep P (a+1)++[false]⟩ =
      some ⟨0,false::([true,true,true]++rep Q b),rep P a++[false]⟩ := by rfl
  have h3 := rightA a ([true,true,true]++rep Q b) [false]
  have h4 : run0 table 2 ⟨0,false::(rep O a++([true,true,true]++rep Q b)),[false]⟩ =
      some (odd (a+2) b) := by
    have h : run0 table 2 ⟨0,false::(rep O a++([true,true,true]++rep Q b)),[false]⟩ =
        some ⟨2,false::true::true::(rep O a++([true,true,true]++rep Q b)),[]⟩ := by rfl
    have e : rep O a++([true,true,true]++rep Q b) = true::(rep O (a+1)++rep Q b) := by
      have er : rep O a++[true] = true::rep O a := by
        symm
        simpa only [O,List.singleton_append] using rotate true [true] a
      change rep O a++([true]++(O++rep Q b)) = true::(rep O (a+1)++rep Q b)
      rw [← List.append_assoc,er,List.cons_append,← List.append_assoc,rep_snoc]
      rfl
    rw [e] at h ⊢
    exact h
  exact ⟨_,by omega,join0 (join0 (join0 h1 h2) h3) h4⟩

theorem oddEnd (a : Nat) : ∃ t, 0<t ∧ run0 table t (odd a 0) = some (even (a+1)) := by
  have h1 := oddCore a 0
  have h2 : run0 table 2 ⟨0,[],rep P (a+1)++[false]⟩ = some ⟨0,false::O,rep P a++[false]⟩ := by rfl
  have h3 := rightA a O [false]
  have h4 : run0 table 2 ⟨0,false::(rep O a++O),[false]⟩ = some (even (a+1)) := by
    rw [rep_snoc O a]
    rfl
  exact ⟨_,by omega,join0 (join0 (join0 h1 h2) h3) h4⟩

theorem evenStep (a : Nat) : ∃ t, 0<t ∧ run0 table t (even a) = some (odd 0 (a+2)) := by
  have h1 : run0 table 10 (even a) = some ⟨0,true::rep O a,[true,false,false]⟩ := by rfl
  have e : true::rep O a = rep O a++[true] := by
    simpa only [O,List.singleton_append] using rotate true [true] a
  rw [e] at h1
  have h2 := left a [true] [true,false,false]
  have er : rep P a++[true,false,false] = rep P (a+1)++[false] := by
    change rep P a++(P++[false]) = rep P (a+1)++[false]
    rw [← List.append_assoc,rep_snoc]
    rfl
  rw [er] at h2
  have h3 : run0 table 4 ⟨0,[true],rep P (a+1)++[false]⟩ =
      some ⟨1,false::Q,rep P (a+1)++[false]⟩ := by
    cases a <;> rfl
  have h4 := rightB (a+1) Q [false]
  have h5 : run0 table 1 ⟨1,false::(rep Q (a+1)++Q),[false]⟩ = some (odd 0 (a+2)) := by
    rw [rep_snoc Q (a+1)]
    rfl
  exact ⟨_,by omega,join0 (join0 (join0 (join0 h1 h2) h3) h4) h5⟩

theorem resolve (a b : Nat) : ∃ t, 0<t ∧ run0 table t (odd a b) = some (even (a+2*b+1)) := by
  induction b generalizing a with
  | zero => simpa using oddEnd a
  | succ b ih =>
    obtain ⟨t,ht,h1⟩ := oddStep a b
    obtain ⟨u,hu,h2⟩ := ih (a+2)
    have h := join0 h1 h2
    rw [show a+2+2*b+1=a+2*(b+1)+1 by omega] at h
    exact ⟨_,by omega,h⟩

theorem grow (b : Nat) : ∃ t, 0<t ∧ run0 table t (odd 0 b) = some (odd 0 (2*b+3)) := by
  obtain ⟨t,ht,h1⟩ := resolve 0 b
  obtain ⟨u,hu,h2⟩ := evenStep (0+2*b+1)
  have h := join0 h1 h2
  rw [show 0+2*b+1+2=2*b+3 by omega] at h
  exact ⟨_,by omega,h⟩

theorem arbitrary (n : Nat) : ∃ t z, n ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some z := by
  have aux : ∀ k : Nat, ∃ t b, k ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some (odd 0 b) := by
    intro k
    induction k with
    | zero => exact ⟨19,2,by omega,by rfl⟩
    | succ k ih =>
      obtain ⟨t,b,ht,h1⟩ := ih
      obtain ⟨u,hu,h2⟩ := grow b
      exact ⟨_,_,by omega,join0 h1 h2⟩
  obtain ⟨t,b,ht,h⟩ := aux n
  exact ⟨t,odd 0 b,ht,h⟩
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table arbitrary m hm
#print axioms arbitrary
#print axioms never
end BB6Coverage.Agent7LF917
