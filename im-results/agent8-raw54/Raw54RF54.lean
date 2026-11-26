import Raw54Return
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.RF54
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,true,5⟩)
  | _,_ => none

-- Z0.l includes the scanned cell, followed by the left half-tape.
inductive Good : List Bool → Prop
  | empty : Good []
  | single (b : Bool) : Good [b]
  | pair (b : Bool) (L : List Bool) : Good L → Good (b::false::L)

def cfg (L : List Bool) (n : Nat) : Z0 :=
  ⟨4,L,rep [true,true] (n+1) ++ [false,true,true]⟩

def nextL (L : List Bool) (n : Nat) : List Bool :=
  if L.headD false then L.tail.tail
  else rep [false,false] n ++ true::L.tail

def nextN (L : List Bool) (n : Nat) : Nat :=
  if L.headD false then n+1 else 0

theorem good_prepend (n : Nat) (L : List Bool) (h : Good L) :
    Good (rep [false,false] n ++ L) := by
  induction n with
  | zero => exact h
  | succ n ih => exact Good.pair false _ ih

theorem good_after (L : List Bool) (n : Nat) (h : Good L) :
    Good (nextL L n) := by
  cases h with
  | empty => exact good_prepend n [true] (Good.single true)
  | single b =>
    cases b
    · exact good_prepend n [true] (Good.single true)
    · exact Good.empty
  | pair b T h =>
    cases b
    · exact good_prepend n (true::false::T) (Good.pair true T h)
    · exact h

theorem first : run0 table 10 ⟨0,[],[]⟩ = some (cfg [] 0) := by rfl

theorem true_step (L : List Bool) (n : Nat) (h : Good L)
    (hb : L.headD false = true) :
    run0 table 4 (cfg L n) = some (cfg L.tail.tail (n+1)) := by
  cases h with
  | empty => simp at hb
  | single b =>
    cases b
    · simp at hb
    · rfl
  | pair b T h =>
    cases b
    · simp at hb
    · rfl

theorem false_entry (L : List Bool) (n : Nat)
    (hb : L.headD false = false) :
    run0 table 2 (cfg L n) =
      some ⟨5,true::false::true::L.tail,rep [true,true] n ++ [false,true,true]⟩ := by
  cases L with
  | nil => rfl
  | cons b T =>
    cases b
    · rfl
    · simp at hb

theorem restore (n : Nat) (T : List Bool) :
    run0 table 10 ⟨5,true::(rep [false,false] n ++ false::true::T),[false,true,true]⟩ =
      some (cfg (rep [false,false] n ++ true::T) 0) := by
  cases n <;> rfl

theorem returns (L : List Bool) (n : Nat) (h : Good L) :
    ∃ t, 0<t ∧ run0 table t (cfg L n) = some (cfg (nextL L n) (nextN L n)) := by
  cases hb : L.headD false
  · have a := false_entry L n hb
    have b := sweepR table 5 [true] [] [true,true] [false,false] 2
      (by intro X Y; rfl) n (false::true::L.tail) [false,true,true]
    simp only [List.nil_append,List.cons_append,List.append_assoc] at b
    have c := restore n L.tail
    have H := join0 (join0 a b) c
    refine ⟨2+2*n+10,by omega,?_⟩
    simpa only [nextL,nextN,hb,Bool.false_eq_true,ite_false] using H
  · refine ⟨4,by omega,?_⟩
    simpa only [nextL,nextN,hb,ite_true] using true_step L n h hb

def data : Nat → List Bool × Nat
  | 0 => ([],0)
  | k+1 => let d := data k; (nextL d.1 d.2,nextN d.1 d.2)

def family (k : Nat) : Z0 := cfg (data k).1 (data k).2

theorem family_good (k : Nat) : Good (data k).1 := by
  induction k with
  | zero => exact Good.empty
  | succ k ih => exact good_after (data k).1 (data k).2 ih

theorem family_next (k : Nat) :
    ∃ t, 0<t ∧ run0 table t (family k) = some (family (k+1)) :=
  returns (data k).1 (data k).2 (family_good k)

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent8Raw54.never_of_returns table family 10 first family_next m hm
#print axioms never
end BB6.Agent8Raw54.RF54
