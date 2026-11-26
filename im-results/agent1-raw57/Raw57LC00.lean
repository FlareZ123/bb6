import Raw58Live
namespace BB6Coverage.Agent1Raw57LC00
open BB6Coverage Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- Raw57 A1=0LC open leaf 0, unary drain. Agent 7.
def table : PartialMachine
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨false,false,2⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => none
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => some (some ⟨false,false,4⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨true,true,4⟩)
  | (4,false) => some (some ⟨false,false,5⟩)
  | (4,true) => some (some ⟨false,false,0⟩)
  | (5,false) => some (some ⟨true,true,5⟩)
  | (5,true) => some (some ⟨false,true,0⟩)
  | _ => none
abbrev U : List Bool := [true]
abbrev Z : List Bool := [false]
abbrev U3 : List Bool := [true,true,true]
abbrev Z3 : List Bool := [false,false,false]
abbrev P : List Bool := [false,false,true,true,false]
def F (k m : Nat) : Z0 := ⟨5,[],false::(rep Z3 k++rep U (m+1))⟩

theorem rep_add (X : List Bool) (n m : Nat) : rep X (n+m) = rep X n ++ rep X m := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp only [show n+1+m=n+m+1 by omega,rep,ih,List.append_assoc]

theorem tripleRep (b : Bool) (n : Nat) : rep [b,b,b] n = rep [b] (3*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      rep [b,b,b] (n+1) = [b,b,b] ++ rep [b,b,b] n := rfl
      _ = rep [b] 3 ++ rep [b] (3*n) := by rw [ih]; rfl
      _ = rep [b] (3+3*n) := (rep_add _ _ _).symm
      _ = rep [b] (3*(n+1)) := by rw [show 3+3*n=3*(n+1) by omega]

theorem beginF (k m : Nat) :
    run0 table 1 (F k m) = some ⟨5,[false,true],rep Z3 k++rep U (m+1)⟩ := by rfl

theorem sweepF (k : Nat) (R : List Bool) :
    run0 table (3*k) ⟨5,[false,true],rep Z3 k++R⟩ =
      some ⟨5,false::(rep U3 k++[true]),R⟩ := by
  exact sweepR table 5 [false] [] Z3 U3 3 (by intro L R; rfl) k [true] R

theorem sweepC (k : Nat) (R : List Bool) :
    run0 table (3*k) ⟨2,rep U3 k++[true],R⟩ =
      some ⟨2,[true],rep Z3 k++R⟩ := by
  exact sweepL table 2 [] [] U3 Z3 3 (by intro L R; rfl) k [true] R

theorem drain (k m : Nat) :
    run0 table (6*k+12) (F k (m+1)) = some (F (k+1) m) := by
  have h1 := beginF k (m+1)
  have h2 := sweepF k (rep U (m+1+1))
  have h3 : run0 table 9 ⟨5,false::(rep U3 k++[true]),rep U (m+1+1)⟩ =
    some ⟨2,rep U3 k++[true],[false,false]++rep U (m+1)⟩ := by rfl
  have h4 := sweepC k ([false,false]++rep U (m+1))
  have h5 : run0 table 2 ⟨2,[true],rep Z3 k++([false,false]++rep U (m+1))⟩ =
    some (F (k+1) m) := by
    change some (⟨5,[],false::false::(rep Z3 k++([false,false]++rep U (m+1)))⟩ : Z0) = _
    rw [← List.append_assoc (rep Z3 k) [false,false] (rep U (m+1))]
    have eq : rep Z3 k ++ [false,false] = [false,false] ++ rep Z3 k := by
      clear h1 h2 h3 h4
      induction k with
      | zero => rfl
      | succ n ih =>
        simp only [rep,List.append_assoc]
        change false::false::false::(rep Z3 n ++ [false,false]) =
          false::false::false::([false,false] ++ rep Z3 n)
        rw [ih]
    rw [eq]
    rfl
  have h := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  rwa [show 1+3*k+9+3*k+2=6*k+12 by omega] at h

theorem sweepD (n : Nat) (L R : List Bool) :
    run0 table (11*n) ⟨3,P++rep U n++L,R⟩ = some ⟨3,P++L,rep U n++R⟩ := by
  exact sweepL table 3 P [] U U 11 (by intro L R; rfl) n L R

theorem growA (n : Nat) :
    run0 table (11*n+10) ⟨0,[false,false]++rep U n,[]⟩ = some ⟨5,[],[false,false,false,false]++rep U (n+1)⟩ := by
  have h1 : run0 table 3 ⟨0,[false,false]++rep U n,[]⟩ = some ⟨3,P++rep U n,[]⟩ := by rfl
  have h2 := sweepD n [] []
  simp only [List.append_nil] at h2
  have h3 : run0 table 7 ⟨3,P,rep U n⟩ = some ⟨5,[],[false,false,false,false]++rep U (n+1)⟩ := by rfl
  have h := join0 (join0 h1 h2) h3
  rwa [show 3+11*n+7=11*n+10 by omega] at h

theorem regenerate (k : Nat) :
    run0 table (36*k+35) (F k 0) = some (F 1 (3*k+2)) := by
  have h1 := beginF k 0
  have h2 := sweepF k [true]
  have h3 : run0 table 2 ⟨5,false::(rep U3 k++[true]),[true]⟩ =
    some ⟨0,[false,false]++rep U (3*k+2),[]⟩ := by
    rw [tripleRep true k]
    change some (⟨0,false::false::true::(rep U (3*k)++[true]),[]⟩ : Z0) = _
    have eq := rep_snoc U (3*k)
    simp only [rep] at eq ⊢
    rw [eq]
    rfl
  have h4 := growA (3*k+2)
  have h := join0 (join0 (join0 h1 h2) h3) h4
  rw [show 1+3*k+2+(11*(3*k+2)+10)=36*k+35 by omega] at h
  exact h

theorem progress (k m : Nat) : ∃ t k' m', 0<t ∧ run0 table t (F k m) = some (F k' m') := by
  cases m with
  | zero => exact ⟨36*k+35,1,3*k+2,by omega,regenerate k⟩
  | succ m => exact ⟨6*k+12,k+1,m,by omega,drain k m⟩

theorem entry : run0 table 10 ⟨0,[],[]⟩ = some (F 1 0) := by rfl
theorem arbitrary (n : Nat) : ∃ t k m, n ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some (F k m) := by
  induction n with
  | zero => exact ⟨10,1,0,by omega,entry⟩
  | succ n ih =>
    obtain ⟨t,k,m,hle,h⟩ := ih
    obtain ⟨u,k',m',hp,hu⟩ := progress k m
    exact ⟨t+u,k',m',by omega,join0 h hu⟩
#print axioms drain
#print axioms regenerate
#print axioms entry
#print axioms arbitrary

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply Agent4Live.never_of_live table _ m hm
  intro n
  obtain ⟨t,k,j,hle,h⟩ := arbitrary n
  exact ⟨t,F k j,hle,h⟩
#print axioms never
end BB6Coverage.Agent1Raw57LC00
