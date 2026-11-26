import Raw54RAClosedCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.ZeroLFCounterGroup
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent8Raw54.RAClosed
inductive V | m2 | m19 | m124 | m89 | m4 | m21 | m126 | m92 | m6 | m23 | m128 | m95 | m93 | m94 | m88 | m91 | m97

def table (v : V) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => match v with
    | .m2 => none
    | .m19 => none
    | .m124 => none
    | .m89 => none
    | .m4 => some (some ⟨false,false,2⟩)
    | .m21 => some (some ⟨false,false,2⟩)
    | .m126 => some (some ⟨false,false,2⟩)
    | .m92 => some (some ⟨false,false,2⟩)
    | .m6 => some (some ⟨true,true,1⟩)
    | .m23 => some (some ⟨true,true,1⟩)
    | .m128 => some (some ⟨true,true,1⟩)
    | .m95 => some (some ⟨true,true,1⟩)
    | .m93 => some (some ⟨false,true,4⟩)
    | .m94 => some (some ⟨true,true,0⟩)
    | .m88 => some (some ⟨true,true,5⟩)
    | .m91 => some (some ⟨true,true,0⟩)
    | .m97 => some (some ⟨true,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => match v with
    | .m2 => some (some ⟨true,true,0⟩)
    | .m19 => some (some ⟨true,true,0⟩)
    | .m124 => some (some ⟨true,true,0⟩)
    | .m89 => some (some ⟨true,true,0⟩)
    | .m4 => none
    | .m21 => none
    | .m126 => none
    | .m92 => none
    | .m6 => none
    | .m23 => none
    | .m128 => none
    | .m95 => none
    | .m93 => none
    | .m94 => none
    | .m88 => none
    | .m91 => none
    | .m97 => none
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => match v with
    | .m2 => some (some ⟨false,false,1⟩)
    | .m19 => some (some ⟨false,false,1⟩)
    | .m124 => some (some ⟨false,false,1⟩)
    | .m89 => some (some ⟨false,false,1⟩)
    | .m4 => some (some ⟨true,true,0⟩)
    | .m21 => some (some ⟨true,true,0⟩)
    | .m126 => some (some ⟨true,true,0⟩)
    | .m92 => some (some ⟨true,true,0⟩)
    | .m6 => some (some ⟨true,true,0⟩)
    | .m23 => some (some ⟨true,true,0⟩)
    | .m128 => some (some ⟨true,true,0⟩)
    | .m95 => some (some ⟨true,true,0⟩)
    | .m93 => some (some ⟨true,true,0⟩)
    | .m94 => some (some ⟨true,true,0⟩)
    | .m88 => some (some ⟨false,false,0⟩)
    | .m91 => some (some ⟨true,false,0⟩)
    | .m97 => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => match v with
    | .m2 => some (some ⟨false,true,0⟩)
    | .m19 => some (some ⟨false,true,0⟩)
    | .m124 => some (some ⟨true,true,4⟩)
    | .m89 => some (some ⟨true,true,0⟩)
    | .m4 => some (some ⟨false,true,0⟩)
    | .m21 => some (some ⟨false,true,0⟩)
    | .m126 => some (some ⟨true,true,4⟩)
    | .m92 => some (some ⟨true,true,0⟩)
    | .m6 => some (some ⟨false,true,0⟩)
    | .m23 => some (some ⟨false,true,0⟩)
    | .m128 => some (some ⟨true,true,4⟩)
    | .m95 => some (some ⟨true,true,0⟩)
    | .m93 => some (some ⟨true,true,0⟩)
    | .m94 => some (some ⟨true,true,0⟩)
    | .m88 => some (some ⟨true,true,0⟩)
    | .m91 => some (some ⟨true,true,0⟩)
    | .m97 => some (some ⟨true,true,0⟩)
  | 5,true => match v with
    | .m2 => some (some ⟨false,true,0⟩)
    | .m19 => some (some ⟨false,true,4⟩)
    | .m124 => some (some ⟨false,true,0⟩)
    | .m89 => some (some ⟨false,true,0⟩)
    | .m4 => some (some ⟨false,true,0⟩)
    | .m21 => some (some ⟨false,true,4⟩)
    | .m126 => some (some ⟨false,true,0⟩)
    | .m92 => some (some ⟨false,true,0⟩)
    | .m6 => some (some ⟨false,true,0⟩)
    | .m23 => some (some ⟨false,true,4⟩)
    | .m128 => some (some ⟨false,true,0⟩)
    | .m95 => some (some ⟨false,true,0⟩)
    | .m93 => some (some ⟨false,true,0⟩)
    | .m94 => some (some ⟨false,true,0⟩)
    | .m88 => some (some ⟨false,true,0⟩)
    | .m91 => some (some ⟨false,true,0⟩)
    | .m97 => some (some ⟨false,true,0⟩)
  | _,_ => none

def m (v : V) : Nat := match v with
  | .m2 => 2
  | .m19 => 2
  | .m124 => 2
  | .m89 => 2
  | .m4 => 3
  | .m21 => 3
  | .m126 => 3
  | .m92 => 3
  | .m6 => 3
  | .m23 => 3
  | .m128 => 3
  | .m95 => 3
  | .m93 => 3
  | .m94 => 3
  | .m88 => 3
  | .m91 => 3
  | .m97 => 3
def extra (v : V) : Nat := match v with
  | .m2 => 1
  | .m19 => 1
  | .m124 => 1
  | .m89 => 1
  | .m4 => 0
  | .m21 => 0
  | .m126 => 0
  | .m92 => 0
  | .m6 => 0
  | .m23 => 0
  | .m128 => 0
  | .m95 => 0
  | .m93 => 1
  | .m94 => 1
  | .m88 => 2
  | .m91 => 1
  | .m97 => 2
def rb (v : V) : Bool := match v with
  | .m2 => false
  | .m19 => false
  | .m124 => false
  | .m89 => false
  | .m4 => false
  | .m21 => false
  | .m126 => false
  | .m92 => false
  | .m6 => true
  | .m23 => true
  | .m128 => true
  | .m95 => true
  | .m93 => false
  | .m94 => false
  | .m88 => false
  | .m91 => false
  | .m97 => false
def toggle (v : V) : Bool := match v with
  | .m2 => false
  | .m19 => false
  | .m124 => false
  | .m89 => true
  | .m4 => false
  | .m21 => false
  | .m126 => false
  | .m92 => true
  | .m6 => false
  | .m23 => false
  | .m128 => false
  | .m95 => true
  | .m93 => true
  | .m94 => true
  | .m88 => true
  | .m91 => true
  | .m97 => true
def qCost (v : V) (f : Bool) : Nat := match v with
  | .m2 => 19
  | .m19 => if f then 23 else 21
  | .m124 => if f then 19 else 21
  | .m89 => 19
  | .m4 => 18
  | .m21 => if f then 22 else 20
  | .m126 => if f then 18 else 20
  | .m92 => 18
  | .m6 => 18
  | .m23 => if f then 22 else 20
  | .m128 => if f then 18 else 20
  | .m95 => 18
  | .m93 => 18
  | .m94 => 18
  | .m88 => 20
  | .m91 => 20
  | .m97 => 18
def exitCost (v : V) : Nat := match v with
  | .m2 => 2
  | .m19 => 4
  | .m124 => 2
  | .m89 => 2
  | .m4 => 2
  | .m21 => 4
  | .m126 => 2
  | .m92 => 2
  | .m6 => 2
  | .m23 => 4
  | .m128 => 2
  | .m95 => 2
  | .m93 => 2
  | .m94 => 2
  | .m88 => 2
  | .m91 => 2
  | .m97 => 2
def popCost (v : V) : Nat := match v with
  | .m2 => 6
  | .m19 => 6
  | .m124 => 6
  | .m89 => 6
  | .m4 => 5
  | .m21 => 5
  | .m126 => 5
  | .m92 => 5
  | .m6 => 3
  | .m23 => 3
  | .m128 => 3
  | .m95 => 3
  | .m93 => 6
  | .m94 => 4
  | .m88 => 7
  | .m91 => 6
  | .m97 => 5
def width (v : V) : Nat := extra v + 3
def nextFlag (v : V) (f : Bool) : Bool := toggle v && !f
def lead (v : V) (n : Nat) : Bool := rb v && (n != 0)
def sz (v : V) (n : Nat) : Nat := m v + width v * n
def z (n : Nat) : List Bool := rep [false] n
def o (n : Nat) : List Bool := rep [true] n
def left (v : V) (n : Nat) (f : Bool) : List Bool := [lead v n] ++ o (sz v n) ++ [false,true,f]
def tail (v : V) : List Nat → List Bool
  | [] => []
  | j::js => z (width v*j+extra v+1) ++ [true,true] ++ tail v js
def code (v : V) : List Nat → List Bool
  | [] => []
  | j::js => z (width v*j+1) ++ [true,true] ++ tail v js
def P (v : V) (n : Nat) (f : Bool) (R : List Bool) : Z0 := ⟨0,left v n f,R⟩
def F (v : V) (w : Nat × Bool × List Nat) : Z0 := P v w.1 w.2.1 (code v w.2.2)
def entryTime (v : V) : Nat := qCost v false
theorem entry (v : V) : run0 (table v) (entryTime v) ⟨0,[],[]⟩ = some (F v (0,toggle v,[])) := by cases v <;> rfl

theorem rep_add' (p : List Bool) (a b : Nat) : rep p (a+b) = rep p a ++ rep p b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [Nat.succ_add,rep,rep,ih,List.append_assoc]

theorem zadd (a b : Nat) : z (a+b) = z a ++ z b := rep_add' _ _ _
theorem oadd (a b : Nat) : o (a+b) = o a ++ o b := rep_add' _ _ _

theorem resetHead (v : V) (n : Nat) (L T : List Bool) :
    run0 (table v) 6 ⟨0,[lead v n] ++ L,[false,false,false] ++ T⟩ =
      some ⟨4,[true] ++ L,[false,true,true] ++ T⟩ := by
  cases v <;> cases n <;> rfl

theorem resetBlankHead (v : V) (n : Nat) (L : List Bool) :
    run0 (table v) 6 ⟨0,[lead v n] ++ L,[]⟩ =
      some ⟨4,[true] ++ L,[false,true,true]⟩ := by
  cases v <;> cases n <;> rfl

theorem eraseOne (v : V) (L R : List Bool) :
    run0 (table v) 1 ⟨4,[true] ++ L,R⟩ = some ⟨4,L,[false] ++ R⟩ := by cases v <;> rfl

theorem resetExit (v : V) (f : Bool) (R : List Bool) :
    run0 (table v) (exitCost v) ⟨4,[false,true,f],[false] ++ R⟩ =
      some ⟨0,[false,false,f],[false] ++ R⟩ := by cases v <;> cases f <;> rfl

theorem resetBase (v : V) (f : Bool) (T : List Bool) :
    run0 (table v) (qCost v f) ⟨0,[false,false,f],z (m v+1) ++ T⟩ =
      some (P v 0 (nextFlag v f) T) := by cases v <;> cases f <;> rfl

theorem popHead (v : V) (n : Nat) (L T : List Bool) :
    run0 (table v) (popCost v) ⟨0,[lead v n] ++ L,[false,true,true] ++ z (extra v) ++ T⟩ =
      some ⟨0,[lead v (n+1)] ++ o (width v) ++ L,T⟩ := by
  cases v <;> cases n <;> rfl

theorem popBlankHead (v : V) (n : Nat) (L : List Bool) :
    run0 (table v) (popCost v) ⟨0,[lead v n] ++ L,[false,true,true]⟩ =
      some ⟨0,[lead v (n+1)] ++ o (width v) ++ L,[]⟩ := by
  cases v <;> cases n <;> rfl

theorem sizeNext (v : V) (n : Nat) : sz v (n+1) = width v + sz v n := by
  simp only [sz,Nat.mul_succ]; omega

theorem pop (v : V) (n : Nat) (f : Bool) (T : List Bool) :
    run0 (table v) (popCost v) (P v n f ([false,true,true] ++ z (extra v) ++ T)) =
      some (P v (n+1) f T) := by
  unfold P left
  rw [sizeNext,oadd]
  simpa only [List.append_assoc] using popHead v n (o (sz v n) ++ [false,true,f]) T

theorem popBlank (v : V) (n : Nat) (f : Bool) :
    run0 (table v) (popCost v) (P v n f [false,true,true]) =
      some (P v (n+1) f []) := by
  unfold P left
  rw [sizeNext,oadd]
  simpa only [List.append_assoc] using popBlankHead v n (o (sz v n) ++ [false,true,f])

-- The head reset is followed by a homogeneous E1 sweep and two fixed exits.
def resetCost (v : V) (n : Nat) (f : Bool) := 6+(sz v n+1)+exitCost v+qCost v f

theorem resetFromE (v : V) (n : Nat) (f : Bool) (T : List Bool) :
    run0 (table v) ((sz v n+1)+exitCost v+qCost v f)
      ⟨4,[true] ++ (o (sz v n) ++ [false,true,f]),[false,true,true] ++ T⟩ =
      some (P v 0 (nextFlag v f) (z (width v*n+1) ++ [true,true] ++ T)) := by
  have h1 := sweepL (table v) 4 [] [] [true] [false] 1 (by
    intro L R; simpa only [List.nil_append] using eraseOne v L R) (sz v n+1) [false,true,f] ([false,true,true] ++ T)
  have h1' : run0 (table v) (sz v n+1)
      ⟨4,[true] ++ (o (sz v n) ++ [false,true,f]),[false,true,true] ++ T⟩ =
      some ⟨4,[false,true,f],z (sz v n+2) ++ [true,true] ++ T⟩ := by
    rw [show sz v n+2 = (sz v n+1)+1 by omega,zadd]
    simpa only [Nat.one_mul,List.nil_append,List.append_assoc,z,o,rep,Nat.add_assoc,List.cons_append] using h1
  have hh : z (sz v n+2) ++ [true,true] ++ T = [false] ++ (z (sz v n+1) ++ [true,true] ++ T) := by
    simp only [z,rep,List.append_assoc]
  have h2 := resetExit v f (z (sz v n+1) ++ [true,true] ++ T)
  rw [← hh] at h2
  have h3 := resetBase v f (z (width v*n+1) ++ [true,true] ++ T)
  have hsplit : z (sz v n+2) ++ [true,true] ++ T = z (m v+1) ++ (z (width v*n+1) ++ [true,true] ++ T) := by
    rw [show sz v n+2=(m v+1)+(width v*n+1) by unfold sz;omega,zadd]
    simp only [List.append_assoc]
  rw [← hsplit] at h3
  exact join0 (join0 h1' h2) h3

theorem reset (v : V) (n : Nat) (f : Bool) (T : List Bool) :
    run0 (table v) (resetCost v n f) (P v n f ([false,false,false] ++ T)) =
      some (P v 0 (nextFlag v f) (z (width v*n+1) ++ [true,true] ++ T)) := by
  have h1 : run0 (table v) 6 (P v n f ([false,false,false] ++ T)) =
      some ⟨4,[true] ++ (o (sz v n) ++ [false,true,f]),[false,true,true] ++ T⟩ := by
    simpa only [P,left,List.append_assoc] using resetHead v n (o (sz v n) ++ [false,true,f]) T
  have h := join0 h1 (resetFromE v n f T)
  simpa only [resetCost,Nat.add_assoc] using h

theorem resetBlank (v : V) (n : Nat) (f : Bool) :
    run0 (table v) (resetCost v n f) (P v n f []) =
      some (P v 0 (nextFlag v f) (z (width v*n+1) ++ [true,true])) := by
  have h1 : run0 (table v) 6 (P v n f []) =
      some ⟨4,[true] ++ (o (sz v n) ++ [false,true,f]),[false,true,true] ++ []⟩ := by
    simpa only [P,left,List.append_assoc,List.append_nil] using resetBlankHead v n (o (sz v n) ++ [false,true,f])
  have h := join0 h1 (resetFromE v n f [])
  simpa only [resetCost,Nat.add_assoc,List.append_nil] using h

theorem codePop (v : V) (j : Nat) (js : List Nat) :
    code v (0::j::js) = [false,true,true] ++ z (extra v) ++ code v (j::js) := by
  simp only [code,tail,Nat.mul_zero,Nat.zero_add]
  rw [show width v*j+extra v+1=extra v+(width v*j+1) by omega,zadd]
  simp only [List.append_assoc]
  rfl

theorem codeReset (v : V) (j : Nat) (js : List Nat) :
    code v ((j+1)::js) = [false,false,false] ++ tail v (j::js) := by
  simp only [code,tail,Nat.mul_succ,width]
  rw [show (extra v+3)*j+(extra v+3)+1 = 3+((extra v+3)*j+extra v+1) by omega,zadd]
  simp only [List.append_assoc]
  rfl

theorem closed (v : V) (x : Nat × Bool × List Nat) :
    ∃ t x', 0 < t ∧ run0 (table v) t (F v x) = some (F v x') := by
  rcases x with ⟨n,f,w⟩
  cases w with
  | nil =>
    refine ⟨resetCost v n f,(0,nextFlag v f,[n]),?_,?_⟩
    · unfold resetCost; omega
    · simpa only [F,code,tail,List.append_nil] using resetBlank v n f
  | cons j js =>
    cases j with
    | zero =>
      refine ⟨popCost v,(n+1,f,js),?_,?_⟩
      · cases v <;> decide
      · cases js with
        | nil => exact popBlank v n f
        | cons j js =>
          simp only [F,codePop]
          exact pop v n f (code v (j::js))
    | succ j =>
      refine ⟨resetCost v n f,(0,nextFlag v f,n::j::js),?_,?_⟩
      · unfold resetCost; omega
      · simp only [F,codeReset]
        exact reset v n f (tail v (j::js))

theorem never (v : V) (M : Machine) (h : compatible (table v) M) : NeverHalts M :=
  neverOfSection (table v) (Nat × Bool × List Nat) (F v) (0,toggle v,[]) (entryTime v) (entry v) (closed v) M h

#print axioms closed
#print axioms never
end BB6.Agent8Raw54.ZeroLFCounterGroup
