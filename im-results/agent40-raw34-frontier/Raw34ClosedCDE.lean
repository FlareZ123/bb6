import GenericClosedGraph
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent40Raw34ClosedCDE
open BB6Coverage

/-!
A new nonhalting subfamily of the genuine Raw34 first-one parent:
  1RB---_1RC---_0RD---_1LC---_------_------

At t=3 the blank run is in D. If C1,D1,E0,E1 are all ordinary
actions returning to C, D, or E, the complete two-symbol control rows
of {C,D,E} are closed. Thus *all completions* of the remaining four
slots are nonhalting, irrespective of tape contents. Unlike a bounded
trace argument, this is an all-time closed-component invariant.

The local finite 25-ary inclusion/exclusion audit is separate from
this source theorem. Neither alone proves the whole Raw34 Cover.
-/

def parent (c1 d1 e0 e1 : Move) : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some c1)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true  => some (some d1)
  | 4,false => some (some e0)
  | 4,true  => some (some e1)
  | _,_ => none

def inside (q : Fin 6) : Prop := q = 2 ∨ q = 3 ∨ q = 4

theorem closed_table
    (c1 d1 e0 e1 : Move)
    (hc : inside c1.next)
    (hd : inside d1.next)
    (he0 : inside e0.next)
    (he1 : inside e1.next) :
    BB6.Agent50GenericClosedGraph.Closed
      (parent c1 d1 e0 e1) inside := by
  intro q b hq
  change q = 2 ∨ q = 3 ∨ q = 4 at hq
  rcases hq with hq | hq | hq
  · subst q
    cases b with
    | false =>
      exact ⟨⟨false,true,3⟩,rfl,Or.inr (Or.inl rfl)⟩
    | true =>
      exact ⟨c1,rfl,hc⟩
  · subst q
    cases b with
    | false =>
      exact ⟨⟨true,false,2⟩,rfl,Or.inl rfl⟩
    | true =>
      exact ⟨d1,rfl,hd⟩
  · subst q
    cases b with
    | false =>
      exact ⟨e0,rfl,he0⟩
    | true =>
      exact ⟨e1,rfl,he1⟩

def start3 : FinRayCfg := {state:=3,head:=3,ones:=[1,0]}

theorem first3 (c1 d1 e0 e1 : Move)
    (m : Machine) (hm : compatible (parent c1 d1 e0 e1) m) :
    run m 3 blank = some (embedFinRay start3) := by
  have h : finitePartialRun (parent c1 d1 e0 e1) 3 finiteBlank =
      some start3 := by rfl
  simpa only [embedFinRay_blank] using
    finitePartialRun_sound (parent c1 d1 e0 e1) m hm finiteBlank start3 3 h

theorem never (c1 d1 e0 e1 : Move)
    (hc : inside c1.next)
    (hd : inside d1.next)
    (he0 : inside e0.next)
    (he1 : inside e1.next)
    (m : Machine) (hm : compatible (parent c1 d1 e0 e1) m) :
    NeverHalts m := by
  exact BB6.Agent50GenericClosedGraph.never_after
    (parent c1 d1 e0 e1) inside
    (closed_table c1 d1 e0 e1 hc hd he0 he1)
    m hm 3 (embedFinRay start3)
    (first3 c1 d1 e0 e1 m hm)
    (by simp [inside,embedFinRay,start3])

def cdeMoves : List Move :=
  [ ⟨false,false,2⟩,⟨false,true,2⟩,⟨true,false,2⟩,⟨true,true,2⟩
  , ⟨false,false,3⟩,⟨false,true,3⟩,⟨true,false,3⟩,⟨true,true,3⟩
  , ⟨false,false,4⟩,⟨false,true,4⟩,⟨true,false,4⟩,⟨true,true,4⟩ ]

theorem twelve_moves : cdeMoves.length = 12 := by decide
theorem moves_distinct : cdeMoves.Nodup := by decide

theorem move_closed (v : Move) (hv : v ∈ cdeMoves) :
    inside v.next := by
  have h : cdeMoves.all (fun w => decide (inside w.next)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp h v hv)

theorem all_cde (c1 d1 e0 e1 : Move)
    (hc : c1 ∈ cdeMoves) (hd : d1 ∈ cdeMoves)
    (he0 : e0 ∈ cdeMoves) (he1 : e1 ∈ cdeMoves)
    (m : Machine) (hm : compatible (parent c1 d1 e0 e1) m) :
    NeverHalts m :=
  never c1 d1 e0 e1
    (move_closed c1 hc) (move_closed d1 hd)
    (move_closed e0 he0) (move_closed e1 he1) m hm

#print axioms closed_table
#print axioms first3
#print axioms never
#print axioms twelve_moves
#print axioms moves_distinct
#print axioms move_closed
#print axioms all_cde

end BB6.Agent40Raw34ClosedCDE
