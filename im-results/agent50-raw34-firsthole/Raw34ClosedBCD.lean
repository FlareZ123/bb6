import SideCycle
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Raw34BCD
open BB6Coverage

/-!
An all-symbol closed B/C/D control component for the Raw34 prefix.
A0=1RB enters B after one blank-start step. When B1,C1,D1 are
independently chosen to have successors only in B/C/D, all symbols
at B,C,D have nonhalting actions that stay in this three-state set.
Every completion is therefore nonhalting, irrespective of its tape.
-/

def parent (b1 c1 d1 : Move) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some b1)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some c1)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true => some (some d1)
  | _,_ => none

def inside (c : Config) : Prop :=
  c.state = 1 ∨ c.state = 2 ∨ c.state = 3

theorem closed_table (b1 c1 d1 : Move)
    (hb : b1.next = 1 ∨ b1.next = 2 ∨ b1.next = 3)
    (hc : c1.next = 1 ∨ c1.next = 2 ∨ c1.next = 3)
    (hd : d1.next = 1 ∨ d1.next = 2 ∨ d1.next = 3)
    (s : Slot) (hs : s.1 = 1 ∨ s.1 = 2 ∨ s.1 = 3) :
    ∃ mv : Move, parent b1 c1 d1 s = some (some mv) ∧
      (mv.next = 1 ∨ mv.next = 2 ∨ mv.next = 3) := by
  rcases s with ⟨q,b⟩
  change q = 1 ∨ q = 2 ∨ q = 3 at hs
  rcases hs with hq | hq | hq
  · subst q
    cases b with
    | false => exact ⟨⟨true,true,2⟩,rfl,Or.inr (Or.inl rfl)⟩
    | true => exact ⟨b1,rfl,hb⟩
  · subst q
    cases b with
    | false => exact ⟨⟨false,true,3⟩,rfl,Or.inr (Or.inr rfl)⟩
    | true => exact ⟨c1,rfl,hc⟩
  · subst q
    cases b with
    | false => exact ⟨⟨true,false,2⟩,rfl,Or.inr (Or.inl rfl)⟩
    | true => exact ⟨d1,rfl,hd⟩

theorem closed_step (b1 c1 d1 : Move)
    (hb : b1.next = 1 ∨ b1.next = 2 ∨ b1.next = 3)
    (hc : c1.next = 1 ∨ c1.next = 2 ∨ c1.next = 3)
    (hd : d1.next = 1 ∨ d1.next = 2 ∨ d1.next = 3)
    (m : Machine) (hm : compatible (parent b1 c1 d1) m)
    (c : Config) (hi : inside c) :
    ∃ z, rawStep m c = some z ∧ inside z := by
  have hs : (readSlot c).1 = 1 ∨
      (readSlot c).1 = 2 ∨ (readSlot c).1 = 3 := by
    simpa [readSlot,inside] using hi
  obtain ⟨mv,hp,hn⟩ := closed_table b1 c1 d1 hb hc hd (readSlot c) hs
  have hmv : m (readSlot c) = some mv := hm (readSlot c) (some mv) hp
  refine ⟨applyMove c mv, by simp [rawStep,hmv],?_⟩
  simpa [inside,applyMove] using hn

theorem closed_run (b1 c1 d1 : Move)
    (hb : b1.next = 1 ∨ b1.next = 2 ∨ b1.next = 3)
    (hc : c1.next = 1 ∨ c1.next = 2 ∨ c1.next = 3)
    (hd : d1.next = 1 ∨ d1.next = 2 ∨ d1.next = 3)
    (m : Machine) (hm : compatible (parent b1 c1 d1) m)
    (n : Nat) (c : Config) (hi : inside c) :
    ∃ z, run m n c = some z ∧ inside z := by
  induction n with
  | zero => exact ⟨c,rfl,hi⟩
  | succ n ih =>
    obtain ⟨z,hz,hi⟩ := ih
    obtain ⟨w,hw,hwinside⟩ :=
      closed_step b1 c1 d1 hb hc hd m hm z hi
    exact ⟨w,by simp [run,hz,hw],hwinside⟩

def start1 : FinRayCfg := {state:=1,head:=1,ones:=[0]}

theorem first1 (b1 c1 d1 : Move)
    (m : Machine) (hm : compatible (parent b1 c1 d1) m) :
    run m 1 blank = some (embedFinRay start1) := by
  have h : finitePartialRun (parent b1 c1 d1) 1 finiteBlank =
      some start1 := by rfl
  simpa only [embedFinRay_blank] using
    finitePartialRun_sound (parent b1 c1 d1) m hm finiteBlank start1 1 h

theorem never (b1 c1 d1 : Move)
    (hb : b1.next = 1 ∨ b1.next = 2 ∨ b1.next = 3)
    (hc : c1.next = 1 ∨ c1.next = 2 ∨ c1.next = 3)
    (hd : d1.next = 1 ∨ d1.next = 2 ∨ d1.next = 3)
    (m : Machine) (hm : compatible (parent b1 c1 d1) m) : NeverHalts m := by
  have h1 := first1 b1 c1 d1 m hm
  have hs : inside (embedFinRay start1) := by
    simp [inside,embedFinRay,start1]
  intro n
  by_cases hn : n ≤ 1
  · cases h : run m n blank with
    | some z => rfl
    | none =>
      have bad := run_none_add m blank n (1-n) h
      have heq : n+(1-n)=1 := by omega
      rw [heq,h1] at bad
      contradiction
  · obtain ⟨z,hz,_⟩ :=
      closed_run b1 c1 d1 hb hc hd m hm (n-1) (embedFinRay start1) hs
    have heq : n=1+(n-1) := by omega
    have hreach : run m n blank = some z := by
      rw [heq,run_append,h1]
      exact hz
    simp [hreach]

def bcdMoves : List Move :=
  [ ⟨false,false,1⟩,⟨false,true,1⟩,⟨true,false,1⟩,⟨true,true,1⟩
  , ⟨false,false,2⟩,⟨false,true,2⟩,⟨true,false,2⟩,⟨true,true,2⟩
  , ⟨false,false,3⟩,⟨false,true,3⟩,⟨true,false,3⟩,⟨true,true,3⟩ ]

theorem count : bcdMoves.length = 12 := by decide
theorem distinct : bcdMoves.Nodup := by decide

theorem move_closed (v : Move) (hv : v ∈ bcdMoves) :
    v.next = 1 ∨ v.next = 2 ∨ v.next = 3 := by
  have h : bcdMoves.all (fun w => decide
      (w.next = 1 ∨ w.next = 2 ∨ w.next = 3)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp h v hv)

theorem all_1728 (b1 c1 d1 : Move)
    (hB : b1 ∈ bcdMoves) (hC : c1 ∈ bcdMoves)
    (hD : d1 ∈ bcdMoves)
    (m : Machine) (hm : compatible (parent b1 c1 d1) m) :
    NeverHalts m :=
  never b1 c1 d1
    (move_closed b1 hB) (move_closed c1 hC) (move_closed d1 hD) m hm

#print axioms closed_table
#print axioms closed_step
#print axioms closed_run
#print axioms first1
#print axioms never
#print axioms count
#print axioms distinct
#print axioms move_closed
#print axioms all_1728
end BB6.Agent50Raw34BCD
