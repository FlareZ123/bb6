import ClosedGrowth
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace BB6.Agent29Raw36B1LCDefect
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent29ClosedGrowth

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨false,false,3⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨true,false,3⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none
abbrev P : List Bool := [true,false]
abbrev D : List Bool := [false,true,true,false]

def frame (R : List Bool) : Z0 := ⟨1,[true],R⟩
theorem pre (R : List Bool) :
    run0 table 9 (frame (P++P++R)) = some ⟨2,[true,true],[false]++P++P++R⟩ := by rfl

theorem rightOne (L R : List Bool) :
    run0 table 10 ⟨2,[true]++L,([false]++P++P)++P++R⟩ =
      some ⟨2,[true]++P++L,([false]++P++P)++R⟩ := by rfl

theorem midDefect (L R : List Bool) :
    run0 table 43 ⟨2,[true]++L,[false]++P++P++D++R⟩ =
      some ⟨3,[false,true]++L,D++P++P++R⟩ := by rfl

theorem midPure (L : List Bool) :
    run0 table 43 ⟨2,[true]++L,[false]++P++P++[false]⟩ =
      some ⟨3,[false,true]++L,D++P++[false]⟩ := by rfl

theorem leftOne (L R : List Bool) :
    run0 table 8 ⟨3,[false,true]++P++L,[]++R⟩ =
      some ⟨3,[false,true]++L,[]++P++R⟩ := by rfl

theorem finish (R : List Bool) :
    run0 table 2 ⟨3,[false,true,true],R⟩ = some (frame (P++R)) := by rfl

theorem phaseDefect (n : Nat) (R : List Bool) :
    run0 table (54+18*n) (frame (P++P++rep P n++D++R)) =
      some (frame (P++rep P n++D++P++P++R)) := by
  have h1 := pre (rep P n++D++R)
  have h2 := sweepR table 2 [true] ([false]++P++P) P P 10 rightOne n [true] (D++R)
  have h3 := midDefect (rep P n++[true]) R
  have h4 := sweepL table 3 [false,true] [] P P 8 leftOne n [true] (D++P++P++R)
  have h5 := finish (rep P n++D++P++P++R)
  simp only [List.nil_append,List.append_assoc] at h1 h2 h3 h4 h5
  have h := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  simpa only [List.append_assoc,show 9+10*n+43+8*n+2=54+18*n by omega] using h

theorem phasePure (n : Nat) :
    run0 table (54+18*n) (frame (P++P++rep P n++[false])) =
      some (frame (P++rep P n++D++P++[false])) := by
  have h1 := pre (rep P n++[false])
  have h2 := sweepR table 2 [true] ([false]++P++P) P P 10 rightOne n [true] [false]
  have h3 := midPure (rep P n++[true])
  have h4 := sweepL table 3 [false,true] [] P P 8 leftOne n [true] (D++P++[false])
  have h5 := finish (rep P n++D++P++[false])
  simp only [List.nil_append,List.append_assoc] at h1 h2 h3 h4 h5
  have h := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  simpa only [List.append_assoc,show 9+10*n+43+8*n+2=54+18*n by omega] using h

theorem clearDefect (R : List Bool) :
    run0 table 62 (frame (P++D++R)) = some (frame (rep P 5++R)) := by rfl

def pure (n : Nat) := frame (rep P (n+2)++[false])
def defect (a b : Nat) := frame (rep P (a+1)++D++rep P b++[false])
def inv (z : Z0) : Prop := (∃ n, z=pure n) ∨ (∃ a b,z=defect a b)
theorem first : run0 table 68 ⟨0,[],[]⟩ = some (pure 2) := by rfl

theorem launch (n : Nat) : run0 table (54+18*n) (pure n) = some (defect n 1) := by
  simpa only [pure,defect,rep,List.append_assoc,List.append_nil] using phasePure n

theorem migrate (a b : Nat) : run0 table (54+18*a) (defect (a+1) b) = some (defect a (b+2)) := by
  have h := phaseDefect a (rep P b++[false])
  have hb : P++P++rep P b = rep P (b+2) := by rfl
  simpa only [defect,rep,List.append_assoc] using h

theorem clear (b : Nat) : run0 table 62 (defect 0 b) = some (pure (b+3)) := by
  have h := clearDefect (rep P b++[false])
  simpa only [defect,pure,rep_add,show b+3+2=5+b by omega,rep,List.append_assoc,List.append_nil] using h

theorem next (z : Z0) (hz : inv z) :
    ∃ t z', 0<t ∧ run0 table t z = some z' ∧ inv z' := by
  rcases hz with ⟨n,rfl⟩ | ⟨a,b,rfl⟩
  · exact ⟨54+18*n,defect n 1,by omega,launch n,Or.inr ⟨n,1,rfl⟩⟩
  · cases a with
    | zero => exact ⟨62,pure (b+3),by omega,clear b,Or.inl ⟨b+3,rfl⟩⟩
    | succ a => exact ⟨54+18*a,defect a (b+2),by omega,migrate a b,Or.inr ⟨a,b+2,rfl⟩⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_invariant table inv 68 (pure 2) first (Or.inl ⟨2,rfl⟩) next m hm
#print axioms never
end BB6.Agent29Raw36B1LCDefect
