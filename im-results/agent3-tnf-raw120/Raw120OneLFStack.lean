import SweepPumping
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace BB6.Agent3Raw120OneLFStack
open BB6Coverage BB6Coverage.Agent31Pump

/-- Leaf 2753: arbitrary stacks of unary runs and short separators. -/
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

abbrev O (n : Nat) := List.replicate n true
abbrev Z (n : Nat) := List.replicate n false

def tailWord : List (Nat × Nat) → List Bool
  | [] => []
  | (b,a)::xs => Z (b+1) ++ (O (a+5) ++ tailWord xs)
def word (a : Nat) (xs : List (Nat × Nat)) := O (a+5) ++ tailWord xs
def Good (R : List Bool) : Prop := ∃ a xs, R = word a xs

theorem prepend (a z : Nat) (R : List Bool) (h : Good R) : Good (O (a+5) ++ (Z z ++ R)) := by
  obtain ⟨b,xs,rfl⟩ := h
  cases z with
  | zero =>
    refine ⟨a+b+5,xs,?_⟩
    simp only [word,List.replicate_zero,List.nil_append,← List.append_assoc,List.replicate_append_replicate]
    rw [show a+5+(b+5)=a+b+5+5 by omega]
  | succ z => exact ⟨a,(z,b)::xs,rfl⟩

def stk : List Nat → List Bool
  | [] => []
  | a::as => true::false::(O (a+4)++stk as)

theorem consume (L R : List Bool) :
    run0 table 5 ⟨5,false::L,true::true::true::R⟩ =
      some ⟨5,false::true::L,true::true::R⟩ := by rfl

theorem scan (n : Nat) (L R : List Bool) :
    run0 table (5*n) ⟨5,false::L,O (n+2)++R⟩ =
      some ⟨5,false::(O n++L),true::true::R⟩ := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have h := join0 (consume L (O n++R)) (ih (true::L))
    rw [show 5*(n+1)=5+5*n by omega,show n+1+2=n+3 by omega]
    have he : O n ++ true::L = true::(O n++L) := by
      change O n ++ ([true]++L) = ([true]++O n)++L
      rw [← List.append_assoc,show [true]=O 1 by rfl,
        List.replicate_append_replicate,List.replicate_append_replicate,Nat.add_comm n 1]
    rw [he] at h
    exact h

theorem boundary (L R : List Bool) :
    run0 table 4 ⟨5,false::L,true::true::false::R⟩ =
      some ⟨5,false::false::true::L,true::R⟩ := by rfl

theorem boundaryEnd (L : List Bool) :
    run0 table 4 ⟨5,false::L,[true,true]⟩ =
      some ⟨5,false::false::true::L,[true]⟩ := by rfl

theorem prepare (a : Nat) (L R : List Bool) :
    run0 table (5*(a+3)+4) ⟨5,false::L,O (a+5)++false::R⟩ =
      some ⟨5,false::false::(O (a+4)++L),true::R⟩ := by
  have h := scan (a+3) L (false::R)
  exact join0 h (boundary (O (a+3)++L) R)

theorem prepareEnd (a : Nat) (L : List Bool) :
    run0 table (5*(a+3)+4) ⟨5,false::L,O (a+5)⟩ =
      some ⟨5,false::false::(O (a+4)++L),[true]⟩ := by
  have h := scan (a+3) L []
  simp only [List.append_nil] at h
  exact join0 h (boundaryEnd (O (a+3)++L))

theorem short1 (L R : List Bool) :
    run0 table 5 ⟨5,false::false::L,true::true::true::R⟩ =
      some ⟨5,false::true::false::L,true::true::R⟩ := by rfl

theorem short2 (L R : List Bool) :
    run0 table 7 ⟨5,false::false::L,true::false::true::true::R⟩ =
      some ⟨5,false::true::false::L,true::true::true::R⟩ := by rfl

theorem long (L R : List Bool) :
    run0 table 10 ⟨5,false::false::L,true::false::false::R⟩ =
      some ⟨5,L,O 5++R⟩ := by rfl

theorem longEnd (L : List Bool) :
    run0 table 10 ⟨5,false::false::L,[true]⟩ =
      some ⟨5,L,O 5⟩ := by rfl

theorem fErase (n : Nat) (L R : List Bool) :
    run0 table n ⟨5,O n++L,R⟩ = some ⟨5,L,Z n++R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h : run0 table 1 ⟨5,true::(O n++L),R⟩ = some ⟨5,O n++L,false::R⟩ := by rfl
    have H := join0 h (ih (false::R))
    rw [show 1+n=n+1 by omega] at H
    have he : Z n ++ false::R = false::(Z n++R) := by
      change Z n ++ ([false]++R) = ([false]++Z n)++R
      rw [← List.append_assoc,show [false]=Z 1 by rfl,
        List.replicate_append_replicate,List.replicate_append_replicate,Nat.add_comm n 1]
    rw [he] at H
    exact H

/-- Descend past every short gap, stopping at a long gap or implicit blanks.
    No bound on the number of short gaps or the lengths of the runs. -/
theorem descend (xs : List (Nat × Nat)) (a : Nat) (stack : List Nat) :
    ∃ t, 0<t ∧ ∃ stack' z R, Good R ∧
      run0 table t ⟨5,false::stk stack,word a xs⟩ =
        some ⟨5,stk stack',Z (z+4)++R⟩ := by
  induction xs generalizing a stack with
  | nil =>
    have h := join0 (prepareEnd a (stk stack)) (longEnd (O (a+4)++stk stack))
    have H := join0 h (fErase (a+4) (stk stack) (O 5))
    refine ⟨5*(a+3)+4+10+(a+4),by omega,stack,a,O 5,⟨0,[],rfl⟩,?_⟩
    simpa only [word,tailWord,List.append_nil] using H
  | cons x xs ih =>
    rcases x with ⟨b,m⟩
    cases b with
    | zero =>
      have h1 := prepare a (stk stack) (word m xs)
      have h2 := short1 (O (a+4)++stk stack) (O (m+3)++tailWord xs)
      obtain ⟨t,ht,st,z,R,hR,h3⟩ := ih m (a::stack)
      refine ⟨5*(a+3)+4+5+t,by omega,st,z,R,hR,?_⟩
      exact join0 (join0 h1 h2) h3
    | succ b =>
      cases b with
      | zero =>
        have h1 := prepare a (stk stack) (false::word m xs)
        have h2 := short2 (O (a+4)++stk stack) (O (m+3)++tailWord xs)
        obtain ⟨t,ht,st,z,R,hR,h3⟩ := ih (m+1) (a::stack)
        refine ⟨5*(a+3)+4+7+t,by omega,st,z,R,hR,?_⟩
        exact join0 (join0 h1 h2) h3
      | succ b =>
        have h1 := prepare a (stk stack) (false::false::(Z b++word m xs))
        have h2 := long (O (a+4)++stk stack) (Z b++word m xs)
        have H := join0 (join0 h1 h2) (fErase (a+4) (stk stack) (O 5++(Z b++word m xs)))
        exact ⟨5*(a+3)+4+10+(a+4),by omega,stack,a,_,prepend 0 b _ ⟨m,xs,rfl⟩,H⟩

theorem resetLocal (L R : List Bool) :
    run0 table 7 ⟨5,false::L,false::false::false::false::R⟩ =
      some ⟨4,O 4++L,true::R⟩ := by rfl

theorem resetRoot (R : List Bool) :
    run0 table 7 ⟨5,[],false::false::false::false::R⟩ =
      some ⟨4,O 4,true::R⟩ := by rfl

theorem eSweep (n : Nat) (L R : List Bool) :
    run0 table n ⟨4,O n++L,R⟩ = some ⟨4,L,O n++R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h : run0 table 1 ⟨4,true::(O n++L),R⟩ = some ⟨4,O n++L,true::R⟩ := by rfl
    have H := join0 h (ih (true::R))
    rw [show 1+n=n+1 by omega] at H
    have he : O n ++ true::R = true::(O n++R) := by
      change O n ++ ([true]++R) = ([true]++O n)++R
      rw [← List.append_assoc,show [true]=O 1 by rfl,
        List.replicate_append_replicate,List.replicate_append_replicate,Nat.add_comm n 1]
    rw [he] at H
    exact H

theorem rootExit (R : List Bool) :
    run0 table 1 ⟨4,[],R⟩ = some ⟨5,[],true::R⟩ := by rfl

theorem skipMarker (L R : List Bool) :
    run0 table 2 ⟨4,true::false::L,R⟩ = some ⟨5,L,true::true::R⟩ := by rfl

theorem eraseMarker (L R : List Bool) :
    run0 table 1 ⟨5,true::L,R⟩ = some ⟨5,L,false::R⟩ := by rfl

theorem twoStep {P : List Nat → Prop} (empty : P []) (single : ∀ a, P [a])
    (step : ∀ a b as, P as → P (a::b::as)) : ∀ xs, P xs
  | [] => empty
  | [a] => single a
  | a::b::as => step a b as (twoStep empty single step as)

/-- Unwind the whole arbitrary stack. Each recursion removes two frames. -/
theorem unwind (stack : List Nat) (z : Nat) (R : List Bool) (hR : Good R) :
    ∃ t, 0<t ∧ ∃ R', Good R' ∧
      run0 table t ⟨5,stk stack,Z (z+4)++R⟩ = some ⟨5,[],R'⟩ := by
  induction stack using twoStep generalizing z R with
  | empty =>
    have h := resetRoot (Z z++R)
    have H := join0 (join0 h (eSweep 4 [] (true::(Z z++R)))) (rootExit (O 5++(Z z++R)))
    refine ⟨12,by omega,_,prepend 1 z R hR,H⟩
  | single a =>
    have h1 := eraseMarker (false::(O (a+4)++stk [])) (Z (z+4)++R)
    have h2 := resetLocal (O (a+4)++stk []) (Z (z+1)++R)
    have h2' : run0 table 7 ⟨5,false::(O (a+4)++stk []),false::(Z (z+4)++R)⟩ =
      some ⟨4,O (a+8)++stk [],true::(Z (z+1)++R)⟩ := by
      have he : O 4++(O (a+4)++stk [])=O (a+8)++stk [] := by
        rw [← List.append_assoc,List.replicate_append_replicate,show 4+(a+4)=a+8 by omega]
      rw [he] at h2
      exact h2
    have H := join0 (join0 h1 h2') (eSweep (a+8) [] (true::(Z (z+1)++R)))
    have h3 := rootExit (O (a+8)++true::(Z (z+1)++R))
    have HH := join0 H h3
    have he : true::(O (a+8)++true::(Z (z+1)++R)) = O (a+10)++(Z (z+1)++R) := by
      have he' : O (a+8)++true::(Z (z+1)++R) = O (a+9)++(Z (z+1)++R) := by
        change O _ ++ ([true]++_) = _
        rw [← List.append_assoc,show [true]=O 1 by rfl,List.replicate_append_replicate]
        rfl
      rw [he']
      rfl
    rw [he] at HH
    exact ⟨1+7+(a+8)+1,by omega,_,prepend (a+5) (z+1) R hR,HH⟩
  | step a b as ih =>
    have h1 := eraseMarker (false::(O (a+4)++stk (b::as))) (Z (z+4)++R)
    have h2 := resetLocal (O (a+4)++stk (b::as)) (Z (z+1)++R)
    have h2' : run0 table 7 ⟨5,false::(O (a+4)++stk (b::as)),false::(Z (z+4)++R)⟩ =
      some ⟨4,O (a+8)++stk (b::as),true::(Z (z+1)++R)⟩ := by
      have he : O 4++(O (a+4)++stk (b::as))=O (a+8)++stk (b::as) := by
        rw [← List.append_assoc,List.replicate_append_replicate,show 4+(a+4)=a+8 by omega]
      rw [he] at h2
      exact h2
    have H := join0 (join0 h1 h2') (eSweep (a+8) (stk (b::as)) (true::(Z (z+1)++R)))
    have h3 := skipMarker (O (b+4)++stk as) (O (a+8)++true::(Z (z+1)++R))
    have HH := join0 H h3
    have he : true::true::(O (a+8)++true::(Z (z+1)++R)) = O (a+11)++(Z (z+1)++R) := by
      have he' : O (a+8)++true::(Z (z+1)++R) = O (a+9)++(Z (z+1)++R) := by
        change O _ ++ ([true]++_) = _
        rw [← List.append_assoc,show [true]=O 1 by rfl,List.replicate_append_replicate]
        rfl
      rw [he']
      rfl
    rw [he] at HH
    have HHH := join0 HH (fErase (b+4) (stk as) (O (a+11)++(Z (z+1)++R)))
    obtain ⟨t,ht,R',hR',h4⟩ := ih b (O (a+11)++(Z (z+1)++R)) (prepend (a+6) (z+1) R hR)
    exact ⟨1+7+(a+8)+2+(b+4)+t,by omega,R',hR',join0 HHH h4⟩

/-- All finite words in the run language have a positive return in it. -/
theorem advance (R : List Bool) (hR : Good R) :
    ∃ t, 0<t ∧ ∃ R', Good R' ∧ run0 table t ⟨5,[],R⟩ = some ⟨5,[],R'⟩ := by
  obtain ⟨a,xs,rfl⟩ := hR
  obtain ⟨t,ht,st,z,S,hS,h1⟩ := descend xs a []
  have h1' : run0 table t ⟨5,[],word a xs⟩ = some ⟨5,stk st,Z (z+4)++S⟩ := by
    cases t with
    | zero => omega
    | succ t => exact h1
  obtain ⟨k,hk,R',hR',h2⟩ := unwind st z S hS
  exact ⟨t+k,by omega,R',hR',join0 h1' h2⟩

def seed : List Bool := O 5
theorem entry : run0 table 10 ⟨0,[],[]⟩ = some ⟨5,[],seed⟩ := by rfl

noncomputable def Step (R : List Bool) (h : Good R) : {v : Nat × List Bool // 0<v.1 ∧ Good v.2 ∧ run0 table v.1 ⟨5,[],R⟩ = some ⟨5,[],v.2⟩} := by
  classical
  exact Classical.choice (by obtain ⟨t,ht,R',hR',hr⟩ := advance R h; exact ⟨⟨(t,R'),ht,hR',hr⟩⟩)

noncomputable def familyData : Nat → {R : List Bool // Good R}
  | 0 => ⟨seed,⟨0,[],rfl⟩⟩
  | n+1 => let prev := familyData n; let nxt := Step prev.val prev.property; ⟨nxt.val.2,nxt.property.2.1⟩
noncomputable def family (n : Nat) : Z0 := ⟨5,[],(familyData n).val⟩
noncomputable def cost (n : Nat) : Nat := (Step (familyData n).val (familyData n).property).val.1

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  refine never_of_growth table family 10 cost entry ?_ ?_ m hm
  · intro n; exact (Step (familyData n).val (familyData n).property).property.1
  · intro n; exact (Step (familyData n).val (familyData n).property).property.2.2

#print axioms advance
#print axioms never
end BB6.Agent3Raw120OneLFStack
