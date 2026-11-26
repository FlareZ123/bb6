import Raw54RAClosedCore
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent8Raw54.ZeroLFSpecialCounter
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent8Raw54.RAClosed
inductive V | m8 | m25 | m98 | m130 | m99
def table (v : V) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => none
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => match v with
    | .m8 => some (some ⟨true,true,0⟩)
    | .m25 => some (some ⟨true,true,0⟩)
    | .m98 => some (some ⟨true,true,0⟩)
    | .m130 => some (some ⟨true,true,0⟩)
    | .m99 => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => match v with
    | .m8 => some (some ⟨false,true,0⟩)
    | .m25 => some (some ⟨false,true,0⟩)
    | .m98 => some (some ⟨true,true,0⟩)
    | .m130 => some (some ⟨true,true,4⟩)
    | .m99 => some (some ⟨true,true,0⟩)
  | 5,true => match v with
    | .m8 => some (some ⟨false,true,0⟩)
    | .m25 => some (some ⟨false,true,4⟩)
    | .m98 => some (some ⟨false,true,0⟩)
    | .m130 => some (some ⟨false,true,0⟩)
    | .m99 => some (some ⟨false,true,0⟩)
  | _,_ => none
def extra (v : V) : Nat := match v with
  | .m8 => 1
  | .m25 => 1
  | .m98 => 1
  | .m130 => 1
  | .m99 => 2
def toggle (v : V) : Bool := match v with
  | .m8 => false
  | .m25 => false
  | .m98 => true
  | .m130 => false
  | .m99 => true
def exitCost (v : V) : Nat := match v with
  | .m8 => 2
  | .m25 => 4
  | .m98 => 2
  | .m130 => 2
  | .m99 => 2
def sResetCost (v : V) : Nat := match v with
  | .m8 => 13
  | .m25 => 15
  | .m98 => 13
  | .m130 => 13
  | .m99 => 13
def popCost (v : V) : Nat := match v with
  | .m8 => 4
  | .m25 => 4
  | .m98 => 4
  | .m130 => 4
  | .m99 => 5
def qCost (v : V) (f : Bool) : Nat := match v with
  | .m8 => 15
  | .m25 => if f then 19 else 17
  | .m98 => 15
  | .m130 => if f then 15 else 17
  | .m99 => 15
def width (v : V) : Nat := extra v+3
def nextFlag (v : V) (f : Bool) : Bool := toggle v && !f
def sz (v : V) (n : Nat) : Nat := 2+width v*n
def z (n : Nat) : List Bool := rep [false] n
def o (n : Nat) : List Bool := rep [true] n
def S (f : Bool) (T : List Bool) : Z0 := ⟨0,[false,false,true,f],[false,true] ++ T⟩
def P (v : V) (n : Nat) (f : Bool) (T : List Bool) : Z0 :=
  match n with
  | 0 => S f T
  | k+1 => ⟨0,[false] ++ o (sz v (k+1)) ++ [false,true,f],T⟩
def tail (v : V) : List Nat → List Bool
  | [] => []
  | j::js => z (width v*j+extra v+1) ++ [true,true] ++ tail v js
def code (v : V) : List Nat → List Bool
  | [] => []
  | j::js => z (width v*j+1) ++ [true,true] ++ tail v js
def F (v : V) (w : Nat × Bool × List Nat) : Z0 := P v w.1 w.2.1 (code v w.2.2)
def entryTime (v : V) : Nat := qCost v false
theorem entry (v : V) : run0 (table v) (entryTime v) ⟨0,[],[]⟩ = some (F v (0,toggle v,[])) := by cases v <;> rfl

theorem rep_add' (p : List Bool) (a b : Nat) : rep p (a+b) = rep p a ++ rep p b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [Nat.succ_add,rep,rep,ih,List.append_assoc]
theorem zadd (a b : Nat) : z (a+b) = z a ++ z b := rep_add' _ _ _
theorem oadd (a b : Nat) : o (a+b) = o a ++ o b := rep_add' _ _ _
theorem resetBase (v : V) (f : Bool) (T : List Bool) :
    run0 (table v) (qCost v f) ⟨0,[false,false,f],[false,false,false] ++ T⟩ = some (S (nextFlag v f) T) := by
  cases v <;> cases f <;> rfl
theorem sReset (v : V) (f : Bool) (T : List Bool) :
    run0 (table v) (sResetCost v) (S f ([false,false,false] ++ T)) =
      some ⟨0,[false,false,f],[false,false,false,false,true,true] ++ T⟩ := by cases v <;> cases f <;> rfl
theorem sResetBlank (v : V) (f : Bool) :
    run0 (table v) (sResetCost v) (S f []) =
      some ⟨0,[false,false,f],[false,false,false,false,true,true]⟩ := by cases v <;> cases f <;> rfl
theorem sPop (v : V) (f : Bool) (T : List Bool) :
    run0 (table v) (popCost v+2) (S f ([false,true,true] ++ z (extra v) ++ T)) =
      some (P v 1 f T) := by cases v <;> cases f <;> rfl
theorem sPopBlank (v : V) (f : Bool) :
    run0 (table v) (popCost v+2) (S f [false,true,true]) =
      some (P v 1 f []) := by cases v <;> cases f <;> rfl
theorem resetHead (v : V) (L T : List Bool) :
    run0 (table v) 6 ⟨0,[false] ++ L,[false,false,false] ++ T⟩ =
      some ⟨4,[true] ++ L,[false,true,true] ++ T⟩ := by cases v <;> rfl
theorem resetBlankHead (v : V) (L : List Bool) :
    run0 (table v) 6 ⟨0,[false] ++ L,[]⟩ = some ⟨4,[true] ++ L,[false,true,true]⟩ := by cases v <;> rfl
theorem eraseOne (v : V) (L R : List Bool) :
    run0 (table v) 1 ⟨4,[true] ++ L,R⟩ = some ⟨4,L,[false] ++ R⟩ := by cases v <;> rfl
theorem resetExit (v : V) (f : Bool) (R : List Bool) :
    run0 (table v) (exitCost v) ⟨4,[false,true,f],[false] ++ R⟩ =
      some ⟨0,[false,false,f],[false] ++ R⟩ := by cases v <;> cases f <;> rfl
theorem popHead (v : V) (L T : List Bool) :
    run0 (table v) (popCost v) ⟨0,[false] ++ L,[false,true,true] ++ z (extra v) ++ T⟩ =
      some ⟨0,[false] ++ o (width v) ++ L,T⟩ := by cases v <;> rfl
theorem popBlankHead (v : V) (L : List Bool) :
    run0 (table v) (popCost v) ⟨0,[false] ++ L,[false,true,true]⟩ =
      some ⟨0,[false] ++ o (width v) ++ L,[]⟩ := by cases v <;> rfl
theorem sizeNext (v : V) (n : Nat) : sz v (n+1) = width v + sz v n := by
  simp only [sz,Nat.mul_succ]; omega

def pCost (v : V) (n : Nat) : Nat := match n with | 0 => popCost v+2 | _+1 => popCost v
theorem pop (v : V) (n : Nat) (f : Bool) (T : List Bool) :
    run0 (table v) (pCost v n) (P v n f ([false,true,true] ++ z (extra v) ++ T)) = some (P v (n+1) f T) := by
  cases n with
  | zero => exact sPop v f T
  | succ n =>
    change run0 (table v) (popCost v) ⟨0,[false] ++ o (sz v (n+1)) ++ [false,true,f],[false,true,true] ++ z (extra v) ++ T⟩ = some ⟨0,[false] ++ o (sz v (n+1+1)) ++ [false,true,f],T⟩
    rw [sizeNext v (n+1),oadd]
    simpa only [List.append_assoc] using popHead v (o (sz v (n+1)) ++ [false,true,f]) T
theorem popBlank (v : V) (n : Nat) (f : Bool) :
    run0 (table v) (pCost v n) (P v n f [false,true,true]) = some (P v (n+1) f []) := by
  cases n with
  | zero => exact sPopBlank v f
  | succ n =>
    change run0 (table v) (popCost v) ⟨0,[false] ++ o (sz v (n+1)) ++ [false,true,f],[false,true,true]⟩ = some ⟨0,[false] ++ o (sz v (n+1+1)) ++ [false,true,f],[]⟩
    rw [sizeNext v (n+1),oadd]
    simpa only [List.append_assoc] using popBlankHead v (o (sz v (n+1)) ++ [false,true,f])

def resetCost (v : V) (n : Nat) (f : Bool) :=
  match n with | 0 => sResetCost v+qCost v f | k+1 => 6+(sz v (k+1)+1)+exitCost v+qCost v f

theorem resetFromE (v : V) (n : Nat) (f : Bool) (T : List Bool) :
    run0 (table v) ((sz v n+1)+exitCost v+qCost v f)
      ⟨4,[true] ++ (o (sz v n) ++ [false,true,f]),[false,true,true] ++ T⟩ =
      some (S (nextFlag v f) (z (width v*n+1) ++ [true,true] ++ T)) := by
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
  have hsplit : z (sz v n+2) ++ [true,true] ++ T = [false,false,false] ++ (z (width v*n+1) ++ [true,true] ++ T) := by
    rw [show sz v n+2=3+(width v*n+1) by unfold sz;omega,zadd]
    simp only [List.append_assoc]
    rfl
  rw [← hsplit] at h3
  exact join0 (join0 h1' h2) h3

theorem reset (v : V) (n : Nat) (f : Bool) (T : List Bool) :
    run0 (table v) (resetCost v n f) (P v n f ([false,false,false] ++ T)) = some (P v 0 (nextFlag v f) (z (width v*n+1) ++ [true,true] ++ T)) := by
  cases n with
  | zero =>
    have h := join0 (sReset v f T) (resetBase v f ([false,true,true] ++ T))
    simpa only [P,resetCost,Nat.mul_zero,Nat.zero_add,z,rep,List.append_nil,List.nil_append,List.cons_append] using h
  | succ n =>
    have h1 := resetHead v (o (sz v (n+1)) ++ [false,true,f]) T
    have h := join0 h1 (resetFromE v (n+1) f T)
    simpa only [P,resetCost,List.append_assoc,Nat.add_assoc] using h

theorem resetBlank (v : V) (n : Nat) (f : Bool) :
    run0 (table v) (resetCost v n f) (P v n f []) = some (P v 0 (nextFlag v f) (z (width v*n+1) ++ [true,true])) := by
  cases n with
  | zero =>
    have h := join0 (sResetBlank v f) (resetBase v f [false,true,true])
    simpa only [P,resetCost,Nat.mul_zero,Nat.zero_add,z,rep,List.append_nil,List.nil_append,List.cons_append] using h
  | succ n =>
    have h1 := resetBlankHead v (o (sz v (n+1)) ++ [false,true,f])
    have h := join0 h1 (resetFromE v (n+1) f [])
    simpa only [P,resetCost,List.append_assoc,List.append_nil,Nat.add_assoc] using h
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
    · cases n <;> cases v <;> simp [resetCost,sResetCost,exitCost] <;> omega
    · simpa only [F,code,tail,List.append_nil] using resetBlank v n f
  | cons j js =>
    cases j with
    | zero =>
      refine ⟨pCost v n,(n+1,f,js),?_,?_⟩
      · cases v <;> cases n <;> simp [pCost,popCost]
      · cases js with
        | nil => exact popBlank v n f
        | cons j js =>
          simp only [F,codePop]
          exact pop v n f (code v (j::js))
    | succ j =>
      refine ⟨resetCost v n f,(0,nextFlag v f,n::j::js),?_,?_⟩
      · cases n <;> cases v <;> simp [resetCost,sResetCost,exitCost] <;> omega
      · simp only [F,codeReset]
        exact reset v n f (tail v (j::js))

theorem never (v : V) (M : Machine) (h : compatible (table v) M) : NeverHalts M :=
  neverOfSection (table v) (Nat × Bool × List Nat) (F v) (0,toggle v,[]) (entryTime v) (entry v) (closed v) M h

#print axioms closed
#print axioms never
end BB6.Agent8Raw54.ZeroLFSpecialCounter
