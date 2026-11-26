import SweepPumping

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39LE7634
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

def table : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨false,true,0⟩)
  | 4, false => some (some ⟨true,false,5⟩)
  | 5, false => some (some ⟨true,true,0⟩)
  | 5, true => some (some ⟨false,false,5⟩)
  | _, _ => none

abbrev Z := rep [false]
abbrev O := rep [true]
abbrev pair : List Bool := [true,false,true]
abbrev atA (L R : List Bool) : Z0 := ⟨0,false::L,R⟩

inductive LeftBody : List Bool → Prop
  | zeros (n : Nat) : LeftBody (Z n)
  | block (g a : Nat) (T : List Bool) (hg : g = 1 ∨ g = 2)
      (ha : 0 < a) (hr : a % 4 = 0 ∨ a % 4 = 3)
      (hT : LeftBody T) : LeftBody (Z g ++ O a ++ T)

def LeftEven (L : List Bool) : Prop :=
  ∃ a T, (a % 4 = 0 ∨ a % 4 = 1) ∧ LeftBody T ∧ L = O a ++ T

def LeftOdd (L : List Bool) : Prop :=
  ∃ a T, (a % 4 = 2 ∨ a % 4 = 3) ∧ LeftBody T ∧ L = O a ++ T

inductive RightTail : List Bool → Prop
  | zeros (n : Nat) : RightTail (Z n)
  | block (g : Nat) (T : List Bool) (hg : 0 < g)
      (hr : g % 4 = 1 ∨ g % 4 = 2) (hT : RightTail T) :
      RightTail (Z g ++ pair ++ T)

inductive RightEven : List Bool → Prop
  | zeros (n : Nat) : RightEven (Z n)
  | first (g : Nat) (T : List Bool) (hg : g % 4 = 0 ∨ g % 4 = 1)
      (hT : RightTail T) : RightEven (Z g ++ pair ++ T)

inductive Good : Z0 → Prop
  | even (L R : List Bool) (hL : LeftEven L) (hR : RightEven R) : Good (atA L R)
  | odd (L T : List Bool) (hL : LeftOdd L) (hT : RightTail T) : Good (atA L (true::T))

private theorem addTwoEven (L : List Bool) (h : LeftEven L) : LeftOdd (true::true::L) := by
  obtain ⟨a,T,ha,hT,rfl⟩ := h
  exact ⟨a+2,T,by omega,hT,rfl⟩

private theorem addTwoOdd (L : List Bool) (h : LeftOdd L) : LeftEven (true::true::L) := by
  obtain ⟨a,T,ha,hT,rfl⟩ := h
  exact ⟨a+2,T,by omega,hT,rfl⟩

private theorem addThree (L : List Bool) (h : LeftEven L) :
    LeftEven (false::false::true::true::true::L) := by
  obtain ⟨a,T,ha,hT,rfl⟩ := h
  exact ⟨0,_,by decide,LeftBody.block 2 (a+3) T (by decide) (by omega) (by omega) hT,rfl⟩

private theorem tailEven (R : List Bool) (h : RightTail R) :
    R.headD false = false ∧ RightEven R.tail := by
  cases h with
  | zeros n =>
    cases n with
    | zero => exact ⟨rfl,RightEven.zeros 0⟩
    | succ n => exact ⟨rfl,RightEven.zeros n⟩
  | block g T hg hr hT =>
    obtain ⟨n,rfl⟩ : ∃ n, g = n+1 := ⟨g-1,by omega⟩
    exact ⟨rfl,RightEven.first n T (by omega) hT⟩

private theorem restoreLeft (T : List Bool) (h : LeftBody T) : LeftEven (true::T.tail) := by
  cases h with
  | zeros n =>
    cases n with
    | zero => exact ⟨1,[],by decide,LeftBody.zeros 0,rfl⟩
    | succ n => exact ⟨1,Z n,by decide,LeftBody.zeros n,rfl⟩
  | block g a T hg ha hr hT =>
    rcases hg with rfl | rfl
    · exact ⟨a+1,T,by omega,hT,rfl⟩
    · exact ⟨1,_,by decide,LeftBody.block 1 a T (by decide) ha hr hT,rfl⟩

-- When B sees a one, the macro consumes it and the following zero.
private theorem takeOne (L T : List Bool) (h : T.headD false = false) :
    run0 table 2 (atA L (true::T)) = some (atA (true::true::L) T.tail) := by
  cases T with
  | nil => rfl
  | cons b T =>
    cases b
    · rfl
    · contradiction

-- Leading 01 followed by the second member of the pair gives the other
-- rightward macro. Its successor also sees zero.
private theorem takePair (L T : List Bool) (h : T.headD false = false) :
    run0 table 5 (atA L (false::pair++T)) =
      some (atA (false::false::true::true::true::L) T.tail) := by
  cases T with
  | nil => rfl
  | cons b T =>
    cases b
    · rfl
    · contradiction

private theorem makeF (L R : List Bool) :
    run0 table 8 (atA L (false::false::false::R)) =
      some ⟨5,true::L,true::false::true::R⟩ := by rfl

private theorem sweepF (a : Nat) (T R : List Bool) :
    run0 table a ⟨5,O a ++ T,R⟩ = some ⟨5,T,Z a ++ R⟩ := by
  simpa only [List.nil_append,Nat.one_mul] using
    (sweepL table 5 [] [] [true] [false] 1 (by intro L R; rfl) a T R)

private theorem finishF (T R : List Bool) (h : T.headD false = false) :
    run0 table 1 ⟨5,T,false::R⟩ = some (atA (true::T.tail) R) := by
  cases T with
  | nil => rfl
  | cons b T =>
    cases b
    · rfl
    · contradiction

private theorem bodyZero (T : List Bool) (h : LeftBody T) : T.headD false = false := by
  cases h with
  | zeros n => cases n <;> rfl
  | block g a T hg ha hr hT => rcases hg with rfl | rfl <;> rfl

-- Complete leftward sweep, including the run of ones adjacent to the head.
private theorem bounceAfter (a : Nat) (T R : List Bool) (hT : LeftBody T) :
    run0 table (a+2) ⟨5,true::(O a ++ T),true::false::true::R⟩ =
      some (atA (true::T.tail) (Z a ++ pair ++ R)) := by
  have h2 := sweepF (a+1) T (true::false::true::R)
  have h3 := finishF T (Z a ++ pair ++ R) (bodyZero T hT)
  have h2' : run0 table (a+1) ⟨5,true::(O a ++ T),true::false::true::R⟩ =
      some ⟨5,T,false::(Z a ++ pair ++ R)⟩ := by
    simpa only [rep,List.singleton_append,List.cons_append,List.nil_append,List.append_assoc] using h2
  have H := join0 h2' h3
  simpa only [show a+1+1=a+2 by omega] using H

private theorem bounce (a : Nat) (T R : List Bool) (hT : LeftBody T) :
    run0 table (a+10) (atA (O a ++ T) (false::false::false::R)) =
      some (atA (true::T.tail) (Z a ++ pair ++ R)) := by
  rw [show a+10=8+(a+2) by omega]
  exact join0 (makeF _ _) (bounceAfter a T R hT)

private theorem bounceZeros (a n : Nat) (T : List Bool) (hT : LeftBody T) :
    run0 table (a+10) (atA (O a ++ T) (Z n)) =
      some (atA (true::T.tail) (Z a ++ pair ++ Z (n-3))) := by
  have h1 : run0 table 8 (atA (O a ++ T) (Z n)) =
      some ⟨5,true::(O a ++ T),true::false::true::Z (n-3)⟩ := by
    rcases n with _ | _ | _ | n <;> rfl
  rw [show a+10=8+(a+2) by omega]
  exact join0 h1 (bounceAfter a T _ hT)

private theorem advanceEven (L R : List Bool) (hL : LeftEven L) (hR : RightEven R) :
    ∃ n z', 0 < n ∧ run0 table n (atA L R) = some z' ∧ Good z' := by
  cases hR with
  | zeros n =>
    obtain ⟨a,T,ha,hT,rfl⟩ := hL
    exact ⟨a+10,_,by omega,bounceZeros a n T hT,
      Good.even _ _ (restoreLeft T hT) (RightEven.first a _ ha (RightTail.zeros (n-3)))⟩
  | first g R hg hR =>
    by_cases h0 : g = 0
    · subst g
      exact ⟨2,_,by decide,takeOne L (false::true::R) rfl,
        Good.odd _ _ (addTwoEven L hL) hR⟩
    by_cases h1 : g = 1
    · subst g
      obtain ⟨hz,ht⟩ := tailEven R hR
      exact ⟨5,_,by decide,takePair L R hz,Good.even _ _ (addThree L hL) ht⟩
    obtain ⟨a,T,ha,hT,rfl⟩ := hL
    obtain ⟨k,rfl⟩ : ∃ k, g = k+3 := ⟨g-3,by omega⟩
    have hk : 0 < k := by omega
    have hkr : k % 4 = 1 ∨ k % 4 = 2 := by omega
    exact ⟨a+10,_,by omega,bounce a T (Z k ++ pair ++ R) hT,
      Good.even _ _ (restoreLeft T hT)
        (RightEven.first a _ ha (RightTail.block k R hk hkr hR))⟩

private theorem advance (z : Z0) (h : Good z) :
    ∃ n z', 0 < n ∧ run0 table n z = some z' ∧ Good z' := by
  cases h with
  | even L R hL hR => exact advanceEven L R hL hR
  | odd L T hL hT =>
    obtain ⟨hz,ht⟩ := tailEven T hT
    exact ⟨2,_,by decide,takeOne L T hz,Good.even _ _ (addTwoOdd L hL) ht⟩

theorem live (k : Nat) : ∃ n z, k ≤ n ∧ run0 table n ⟨0,[],[]⟩ = some z ∧ Good z := by
  induction k with
  | zero =>
    refine ⟨10,atA [true] pair,by decide,rfl,Good.even _ _ ?_ ?_⟩
    · exact ⟨1,[],by decide,LeftBody.zeros 0,rfl⟩
    · exact RightEven.first 0 [] (by decide) (RightTail.zeros 0)
  | succ k ih =>
    obtain ⟨n,z,hn,hz,hg⟩ := ih
    obtain ⟨t,z',ht,hr,hg'⟩ := advance z hg
    exact ⟨n+t,z',by omega,join0 hz hr,hg'⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,hr,_⟩ := live n
  have hz : (zrun table t start).map project = some z := (run_project table t start).trans hr
  cases h : zrun table t start with
  | none => simp [h] at hz
  | some z' =>
    have H := zrun_sound table m hm t start z' h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms never
end BB6.Agent11Raw39LE7634
