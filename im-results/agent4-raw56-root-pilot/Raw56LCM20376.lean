import SweepPumping

namespace BB6.Agent4Raw56LCM20376
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

def p : PartialMachine := fun (q,b) =>
  match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => none
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,false,2⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨false,true,5⟩)
  | _,_ => none

def O : List Bool := [true,true,true,true]
def Zeros : List Bool := [false,false,false,false]
def R (n : Nat) := [true,true] ++ rep O n ++ [false]
def G (n : Nat) (L : List Bool) : Z0 := ⟨0,L,R n⟩

-- The right sweep converts four ones to four zeros and preserves its frame.
theorem sweep_block (L T : List Bool) :
    run0 p 4 ⟨5,[true,false]++L,O++T⟩ =
      some ⟨5,[true,false]++Zeros++L,T⟩ := rfl

theorem end_sweep (L : List Bool) :
    run0 p 14 ⟨5,[true,false]++L,[false]⟩ = some ⟨0,L,R 0⟩ := by
  cases L <;> rfl

theorem pre0 (b : Bool) (L T : List Bool) :
    run0 p 12 ⟨0,[false,false,false,b]++L,[true,true]++T⟩ =
      some ⟨5,[true,false,false,false,true,b]++L,T⟩ := rfl

theorem pre1 (L T : List Bool) :
    run0 p 16 ⟨0,[false,false,true,false]++L,[true,true]++T⟩ =
      some ⟨5,[true,false,false,false,false,true]++L,T⟩ := rfl

theorem preEmpty (T : List Bool) :
    run0 p 12 ⟨0,[],[true,true]++T⟩ =
      some ⟨5,[true,false,false,false,true],T⟩ := rfl

theorem preShort (T : List Bool) :
    run0 p 16 ⟨0,[false,false,true],[true,true]++T⟩ =
      some ⟨5,[true,false,false,false,false,true],T⟩ := rfl

theorem carry (n : Nat) (L : List Bool) :
    run0 p 10 (G n ([false,false,true,true]++L)) = some (G (n+1) L) := by
  simp only [G,R,rep,List.append_assoc]
  rfl

theorem finish (n : Nat) (L : List Bool) :
    run0 p (4*n+14) ⟨5,[true,false]++L,rep O n++[false]⟩ =
      some (G 0 (rep Zeros n++L)) := by
  have H := sweepR p 5 [true,false] [] O Zeros 4 (by simpa using sweep_block) n L [false]
  simp only [List.nil_append] at H
  exact join0 H (end_sweep (rep Zeros n++L))

theorem inc0 (n : Nat) (b : Bool) (L : List Bool) :
    run0 p (12+(4*n+14)) (G n ([false,false,false,b]++L)) =
      some (G 0 (rep Zeros n++([false,false,true,b]++L))) := by
  exact join0 (pre0 b L (rep O n++[false])) (finish n ([false,false,true,b]++L))

theorem inc1 (n : Nat) (L : List Bool) :
    run0 p (16+(4*n+14)) (G n ([false,false,true,false]++L)) =
      some (G 0 (rep Zeros n++([false,false,false,true]++L))) := by
  exact join0 (pre1 L (rep O n++[false])) (finish n ([false,false,false,true]++L))

theorem empty_return (n : Nat) :
    run0 p (12+(4*n+14)) (G n []) =
      some (G 0 (rep Zeros n++[false,false,true])) := by
  exact join0 (preEmpty (rep O n++[false])) (finish n [false,false,true])

theorem short_return (n : Nat) :
    run0 p (16+(4*n+14)) (G n [false,false,true]) =
      some (G 0 (rep Zeros n++[false,false,false,true])) := by
  exact join0 (preShort (rep O n++[false])) (finish n [false,false,false,true])

/-- The left tape consists of base-four digits (00ab), with an optional
    final truncated digit 001, and the right tape records a carry depth. -/
inductive Good : List Bool → Prop
  | empty : Good []
  | short : Good [false,false,true]
  | digit (a b : Bool) (L : List Bool) : Good L → Good ([false,false,a,b]++L)

theorem zero_prefix (n : Nat) (L : List Bool) (h : Good L) :
    Good (rep Zeros n++L) := by
  induction n with
  | zero => exact h
  | succ n ih => simpa only [rep,Zeros,List.append_assoc] using Good.digit false false (rep Zeros n++L) ih

theorem closed (n : Nat) (L : List Bool) (h : Good L) :
    ∃ t n' L', 0 < t ∧ Good L' ∧ run0 p t (G n L) = some (G n' L') := by
  cases h with
  | empty => exact ⟨_,0,_,by omega,zero_prefix n _ Good.short,empty_return n⟩
  | short => exact ⟨_,0,_,by omega,zero_prefix n _ (Good.digit false true [] Good.empty),short_return n⟩
  | digit a b L hL =>
    cases a with
    | false => exact ⟨_,0,_,by omega,zero_prefix n _ (Good.digit true b L hL),inc0 n b L⟩
    | true =>
      cases b with
      | false => exact ⟨_,0,_,by omega,zero_prefix n _ (Good.digit false true L hL),inc1 n L⟩
      | true => exact ⟨10,n+1,L,by decide,hL,carry n L⟩

theorem entry : run0 p 27 ⟨0,[],[]⟩ = some (G 0 [false,false,true]) := rfl

theorem live_prefix (k : Nat) :
    ∃ t n L, k ≤ t ∧ Good L ∧ run0 p t ⟨0,[],[]⟩ = some (G n L) := by
  induction k with
  | zero => exact ⟨27,0,_,by decide,Good.short,entry⟩
  | succ k ih =>
    obtain ⟨t,n,L,ht,hL,hr⟩ := ih
    obtain ⟨u,n',L',hu,hL',hs⟩ := closed n L hL
    exact ⟨t+u,n',L',by omega,hL',join0 hr hs⟩

/-- Original-machine theorem for every completion of the undefined A1 slot. -/
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  intro k
  obtain ⟨t,n,L,ht,_,hr⟩ := live_prefix k
  have hz : (zrun p t start).map project = some (G n L) :=
    (run_project p t start).trans hr
  cases h : zrun p t start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound p m hm t start z h
    rw [start_embed] at H
    rw [show t=k+(t-k) by omega,run_append] at H
    cases he : run m k blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms never
end BB6.Agent4Raw56LCM20376
