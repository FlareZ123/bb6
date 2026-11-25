import BlockPump

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BB6.Agent2Raw124ZeroLFPairReturn
open BB6Coverage BB6Coverage.Agent50Pump

/-- The fifth of the five remaining F1=0LF, F0=1RB hard leaves.
    B1 remains completely unspecified. -/
def p4 : PartialMachine := fun s =>
  ([some (some ⟨true,true,1⟩), some (some ⟨false,true,3⟩),
    some (some ⟨true,true,2⟩), none,
    some (some ⟨false,true,3⟩), some (some ⟨true,false,0⟩),
    some (some ⟨true,false,3⟩), some (some ⟨true,true,4⟩),
    some (some ⟨true,true,1⟩), some (some ⟨true,false,5⟩),
    some (some ⟨true,true,1⟩), some (some ⟨false,false,5⟩)] :
    List (Option Transition))[2*s.1.val+s.2.toNat]?.getD none

/-- Each bit is represented by two identical raw cells, nearest first. -/
def pairs : List Bool → List Bool
  | [] => []
  | b::bs => b::b::pairs bs

def sec (x : List Bool) : HZ := ⟨5,[],false::false::false::false::false::pairs x⟩
def front (l x : List Bool) : HZ := ⟨5,false::l,false::true::pairs x⟩
def back (l x : List Bool) : HZ := ⟨5,false::l,false::false::false::pairs x⟩

/-- A nonempty collection of odd-length runs of ones, separated by single zeros.
    Each run has length at least three. -/
inductive Back : List Bool → Prop where
  | last (n : Nat) : Back (List.replicate (2*n+3) true)
  | more (n : Nat) {l : List Bool} : Back l →
      Back (List.replicate (2*n+3) true ++ false::l)

/-- Forward sweep stack: each iteration pushes 11 or 1101. -/
inductive Front : List Bool → Prop where
  | base : Front [true,true]
  | two {l : List Bool} : Front l → Front (true::true::l)
  | block {l : List Bool} : Front l → Front (true::true::false::true::l)

theorem replicate_two (n : Nat) :
    true::true::List.replicate (2*n+3) true = List.replicate (2*(n+1)+3) true := by
  rw [show 2*(n+1)+3 = (2*n+3)+2 by omega]
  rfl

theorem back_two {l : List Bool} (h : Back l) : Back (true::true::l) := by
  cases h with
  | last n => rw [replicate_two]; exact .last (n+1)
  | more n h =>
    change Back ((true::true::List.replicate (2*n+3) true) ++ false::_)
    rw [replicate_two]
    exact .more (n+1) h

theorem front_back {l : List Bool} (h : Front l) : Back (true::l) := by
  induction h with
  | base => exact .last 0
  | two h ih => exact back_two ih
  | block h ih => exact .more 0 ih

/-- The eleven fixed transitions are used here; no B1 query occurs. -/
theorem enter (x : List Bool) :
    hrun p4 15 (sec x) = some (front [true,true] (false::x)) := by
  rfl

theorem consumeOne (l x : List Bool) :
    hrun p4 14 (front l (true::x)) = some (front (true::true::l) x) := by
  rfl

theorem consumeZeroOne (l x : List Bool) :
    hrun p4 12 (front l (false::true::x)) =
      some (front (true::true::false::true::l) x) := by
  rfl

theorem stopZeros (l x : List Bool) :
    hrun p4 15 (front l (false::false::x)) = some (back (true::l) (true::x)) := by
  rfl

theorem stopEmpty (l : List Bool) :
    hrun p4 15 (front l []) = some (back (true::l) [true]) := by
  rfl

theorem stopSingleZero (l : List Bool) :
    hrun p4 15 (front l [false]) = some (back (true::l) [true]) := by
  rfl

/-- The forward scan consumes at least one pair per recursion.  Missing
    right-hand cells are genuinely blank, handled by the two base cases. -/
theorem front_complete (x l : List Bool) (hl : Front l) :
    ∃ k l' y, 0 < k ∧ Back l' ∧ hrun p4 k (front l x) = some (back l' y) := by
  cases x with
  | nil => exact ⟨15,true::l,[true],by decide,front_back hl,stopEmpty l⟩
  | cons b x =>
    cases b with
    | true =>
      obtain ⟨k,l',y,hk,hb,hr⟩ := front_complete x (true::true::l) (.two hl)
      exact ⟨14+k,l',y,by omega,hb,hjoin (consumeOne l x) hr⟩
    | false =>
      cases x with
      | nil => exact ⟨15,true::l,[true],by decide,front_back hl,stopSingleZero l⟩
      | cons b x =>
        cases b with
        | false => exact ⟨15,true::l,true::x,by decide,front_back hl,stopZeros l x⟩
        | true =>
          obtain ⟨k,l',y,hk,hb,hr⟩ := front_complete x (true::true::false::true::l) (.block hl)
          exact ⟨12+k,l',y,by omega,hb,hjoin (consumeZeroOne l x) hr⟩
termination_by x.length

/-- First seven moves of the backward phase create a fresh pair of ones. -/
theorem back_init (l x : List Bool) :
    hrun p4 7 (back l x) = some ⟨5,true::true::l,pairs (true::x)⟩ := by
  rfl

theorem sweepOnes (n : Nat) (l r : List Bool) :
    hrun p4 n ⟨5,List.replicate n true ++ l,r⟩ =
      some ⟨5,l,List.replicate n false ++ r⟩ := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    have hh : hrun p4 1 ⟨5,List.replicate (n+1) true ++ l,r⟩ =
        some ⟨5,List.replicate n true ++ l,false::r⟩ := by rfl
    have h := hjoin hh (ih (false::r))
    rw [show 1+n=n+1 by omega] at h
    rw [List.replicate_succ' (n:=n) (a:=false), List.append_assoc]
    exact h

/-- The zeros produced by an odd run have length five plus a paired
    zero suffix.  This is the key parity-preserving invariant. -/
theorem pairsZeros (n : Nat) (x : List Bool) :
    pairs (List.replicate n false ++ x) = List.replicate (2*n) false ++ pairs x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1) = 2*n+2 by omega]
    change false::false::pairs (List.replicate n false ++ x) =
      false::false::(List.replicate (2*n) false ++ pairs x)
    rw [ih]

theorem zeroPairs (n : Nat) (x : List Bool) :
    List.replicate (2*n+5) false ++ pairs x =
      false::false::false::false::false::pairs (List.replicate n false ++ x) := by
  rw [pairsZeros]
  rfl

theorem back_last (n : Nat) (x : List Bool) :
    hrun p4 (7+(2*n+5)) (back (List.replicate (2*n+3) true) x) =
      some (sec (List.replicate n false ++ true::x)) := by
  have h := sweepOnes (2*n+5) [] (pairs (true::x))
  have h0 : hrun p4 (2*n+5) ⟨5,true::true::List.replicate (2*n+3) true,pairs (true::x)⟩ =
      some (sec (List.replicate n false ++ true::x)) := by
    rw [zeroPairs n (true::x)] at h
    simpa only [List.append_nil,List.replicate_succ,sec] using h
  exact hjoin (back_init _ _) h0

theorem back_more (n : Nat) (l x : List Bool) :
    hrun p4 (7+(2*n+5)) (back (List.replicate (2*n+3) true ++ false::l) x) =
      some (back l (false::List.replicate n false ++ true::x)) := by
  have h := sweepOnes (2*n+5) (false::l) (pairs (true::x))
  have h0 : hrun p4 (2*n+5) ⟨5,true::true::(List.replicate (2*n+3) true ++ false::l),pairs (true::x)⟩ =
      some (back l (false::List.replicate n false ++ true::x)) := by
    rw [zeroPairs n (true::x)] at h
    exact h
  exact hjoin (back_init _ _) h0

/-- Every legal odd-run stack is cleared by a finite backward scan. -/
theorem back_complete {l : List Bool} (hl : Back l) (x : List Bool) :
    ∃ k y, 0 < k ∧ hrun p4 k (back l x) = some (sec y) := by
  induction hl generalizing x with
  | last n => exact ⟨7+(2*n+5),List.replicate n false ++ true::x,by omega,back_last n x⟩
  | more n hl ih =>
    obtain ⟨k,y,hk,hr⟩ := ih (false::List.replicate n false ++ true::x)
    exact ⟨7+(2*n+5)+k,y,by omega,hjoin (back_more n _ x) hr⟩

/-- An arbitrary finite paired word is returned to another paired word,
    by a positive finite number of successful primitive moves. -/
theorem section_complete (x : List Bool) :
    ∃ k y, 0 < k ∧ hrun p4 k (sec x) = some (sec y) := by
  obtain ⟨k,l,y,hk,hl,hr⟩ := front_complete (false::x) [true,true] .base
  obtain ⟨t,z,ht,hs⟩ := back_complete hl y
  exact ⟨15+k+t,z,by omega,hjoin (hjoin (enter x) hr) hs⟩

theorem root : hrun p4 42 ⟨0,[],[]⟩ = some (sec [true,true]) := by rfl

theorem arbitrary_live (n : Nat) :
    ∃ k x, n ≤ k ∧ hrun p4 k ⟨0,[],[]⟩ = some (sec x) := by
  induction n with
  | zero => exact ⟨42,[true,true],by decide,root⟩
  | succ n ih =>
    obtain ⟨k,x,hk,hr⟩ := ih
    obtain ⟨t,y,ht,hs⟩ := section_complete x
    exact ⟨k+t,y,by omega,hjoin hr hs⟩

#print axioms section_complete
#print axioms arbitrary_live
open BB6Coverage.Agent50Zipper

theorem blank_eq : embed (HZ.at ⟨0,[],[]⟩ 0) = blank := by
  unfold embed HZ.at blank
  congr 1
  funext x
  simp [atCell]

/-- Every one of the 25 completions of the unspecified B1 slot is nonhalting. -/
theorem neverHard4 (m : Machine) (hm : compatible p4 m) : NeverHalts m := by
  intro n
  obtain ⟨k,x,hk,Hk⟩ := arbitrary_live n
  obtain ⟨h',H'⟩ := hrun_sound p4 k _ _ 0 Hk
  have H := zrun_sound p4 m hm k _ _ H'
  rw [blank_eq] at H
  rw [show k=n+(k-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some z => rfl

theorem coverHard4 (bound : Nat) : Cover (DecidedBelow bound) p4 :=
  .leaf _ (fun m hm => Or.inl (neverHard4 m hm))

#print axioms neverHard4
#print axioms coverHard4
end BB6.Agent2Raw124ZeroLFPairReturn
