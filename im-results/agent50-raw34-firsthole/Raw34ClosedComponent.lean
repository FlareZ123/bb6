import SideCycle
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Raw34Closed
open BB6Coverage

/-!
A general closed-state proof for the Raw34 C1/D1 independent choices.

Starting blank, A0=1RB, B0=1RC, C0=0RD bring the head to
state D in exactly three steps. If the other two missing C1/D1
transitions have their successor in {C,D}, then states C and D
form a closed all-symbol nonhalting component, independently of
the tape contents and every other state transition.
-/

def parent (c1 d1 : Move) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some c1)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true => some (some d1)
  | _,_ => none

def inside (c : Config) : Prop := c.state = 2 ∨ c.state = 3

theorem closed_table (c1 d1 : Move)
    (hc : c1.next = 2 ∨ c1.next = 3)
    (hd : d1.next = 2 ∨ d1.next = 3)
    (s : Slot) (hs : s.1 = 2 ∨ s.1 = 3) :
    ∃ mv : Move, parent c1 d1 s = some (some mv) ∧
      (mv.next = 2 ∨ mv.next = 3) := by
  rcases s with ⟨q,b⟩
  change q = 2 ∨ q = 3 at hs
  rcases hs with hq | hq
  · subst q
    cases b with
    | false => exact ⟨⟨false,true,3⟩,rfl,Or.inr rfl⟩
    | true => exact ⟨c1,rfl,hc⟩
  · subst q
    cases b with
    | false => exact ⟨⟨true,false,2⟩,rfl,Or.inl rfl⟩
    | true => exact ⟨d1,rfl,hd⟩

theorem closed_step (c1 d1 : Move)
    (hc : c1.next = 2 ∨ c1.next = 3)
    (hd : d1.next = 2 ∨ d1.next = 3)
    (m : Machine) (hm : compatible (parent c1 d1) m)
    (c : Config) (hi : inside c) :
    ∃ d, rawStep m c = some d ∧ inside d := by
  have hs : (readSlot c).1 = 2 ∨ (readSlot c).1 = 3 := by
    simpa [readSlot,inside] using hi
  obtain ⟨mv,hp,hn⟩ := closed_table c1 d1 hc hd (readSlot c) hs
  have hmv : m (readSlot c) = some mv := hm (readSlot c) (some mv) hp
  refine ⟨applyMove c mv, by simp [rawStep,hmv], ?_⟩
  simpa [inside,applyMove] using hn

theorem closed_run (c1 d1 : Move)
    (hc : c1.next = 2 ∨ c1.next = 3)
    (hd : d1.next = 2 ∨ d1.next = 3)
    (m : Machine) (hm : compatible (parent c1 d1) m)
    (n : Nat) (c : Config) (hi : inside c) :
    ∃ d, run m n c = some d ∧ inside d := by
  induction n with
  | zero => exact ⟨c,rfl,hi⟩
  | succ n ih =>
    obtain ⟨d,hr,hinside⟩ := ih
    obtain ⟨e,hs,hnext⟩ :=
      closed_step c1 d1 hc hd m hm d hinside
    exact ⟨e, by simp [run,hr,hs],hnext⟩

def start3 : FinRayCfg := {state:=3,head:=3,ones:=[1,0]}

theorem first3 (c1 d1 : Move)
    (m : Machine) (hm : compatible (parent c1 d1) m) :
    run m 3 blank = some (embedFinRay start3) := by
  have h : finitePartialRun (parent c1 d1) 3 finiteBlank =
      some start3 := by rfl
  simpa only [embedFinRay_blank] using
    finitePartialRun_sound (parent c1 d1) m hm finiteBlank start3 3 h

theorem never (c1 d1 : Move)
    (hc : c1.next = 2 ∨ c1.next = 3)
    (hd : d1.next = 2 ∨ d1.next = 3)
    (m : Machine) (hm : compatible (parent c1 d1) m) : NeverHalts m := by
  have h3 := first3 c1 d1 m hm
  have hs : inside (embedFinRay start3) := by simp [inside,embedFinRay,start3]
  intro n
  by_cases hn : n ≤ 3
  · cases h : run m n blank with
    | some d => rfl
    | none =>
      have bad := run_none_add m blank n (3-n) h
      have heq : n+(3-n)=3 := by omega
      rw [heq,h3] at bad
      contradiction
  · obtain ⟨d,hdone,_⟩ :=
      closed_run c1 d1 hc hd m hm (n-3) (embedFinRay start3) hs
    have heq : n=3+(n-3) := by omega
    have hreach : run m n blank = some d := by
      rw [heq,run_append,h3]
      exact hdone
    simp [hreach]

def closedMoves : List Move :=
  [ ⟨false,false,2⟩,⟨false,true,2⟩,⟨true,false,2⟩,⟨true,true,2⟩
  , ⟨false,false,3⟩,⟨false,true,3⟩,⟨true,false,3⟩,⟨true,true,3⟩ ]

theorem eight_moves : closedMoves.length = 8 := by decide

theorem moves_distinct : closedMoves.Nodup := by decide

theorem moves_closed (v : Move) (hv : v ∈ closedMoves) :
    v.next = 2 ∨ v.next = 3 := by
  have h : closedMoves.all (fun w =>
      decide (w.next = 2 ∨ w.next = 3)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp h v hv)

theorem all_sixtyfour (c1 d1 : Move)
    (h1 : c1 ∈ closedMoves) (h2 : d1 ∈ closedMoves)
    (m : Machine) (hm : compatible (parent c1 d1) m) :
    NeverHalts m :=
  never c1 d1 (moves_closed c1 h1) (moves_closed d1 h2) m hm

#print axioms closed_table
#print axioms closed_step
#print axioms closed_run
#print axioms first3
#print axioms never
#print axioms eight_moves
#print axioms moves_distinct
#print axioms moves_closed
#print axioms all_sixtyfour

end BB6.Agent50Raw34Closed
