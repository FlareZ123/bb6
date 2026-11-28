import Box27SliceCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent49.Box27EasyE0
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent13.Box17 (decode leafCheck Witness)
open BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent49.Box27Slice (terminal_sound)

/-- Twenty E0 codes have direct finite witnesses. A1,B1,E1,F0,F1 remain free. -/
def table (e : Fin 25) : PartialMachine := fun s => match s with
  | (0,false) => some (decode 8)
  | (1,false) => some (decode 11)
  | (2,false) | (2,true) => some (decode 13)
  | (3,false) => some (decode 14)
  | (3,true) => some (decode 17)
  | (4,false) => some (decode e)
  | _ => none

def easy : List (Fin 25) := [0, 1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]
def witness (e : Fin 25) : Witness :=
  match e.val with
  | 0 => .halt 6
  | 1 => .cycle 0 7 false 1
  | 2 => .cycle 0 7 true (-1)
  | 4 => .cycle 5 5 false 2
  | 5 => .cycle 3 6 false 1
  | 6 => .cycle 3 6 true (-1)
  | 7 => .cycle 3 6 false 1
  | 8 => .cycle 1 6 true (-1)
  | 9 => .cycle 8 1 true (-2)
  | 10 => .cycle 8 1 true 0
  | 11 => .cycle 3 5 false 1
  | 12 => .cycle 5 3 false 1
  | 13 => .cycle 7 1 true (-1)
  | 14 => .cycle 7 1 true 1
  | 15 => .cycle 4 3 false 1
  | 16 => .cycle 7 1 true 1
  | 17 => .cycle 6 1 false 0
  | 18 => .cycle 6 1 true 0
  | 19 => .cycle 6 1 false 0
  | 20 => .cycle 6 1 true 0
  | _ => .halt 0

theorem checks : ∀ e : Fin 25, e ∈ easy →
    leafCheck 108 #[] (table e) (witness e) = true := by decide

theorem bound (e : Fin 25) (he : e ∈ easy) (m : Machine)
    (hm : compatible (table e) m) : WeightedBound 108 m :=
  terminal_sound 108 (table e) (witness e) (checks e he) m hm

theorem from_source (e : Fin 25) (m : Machine)
    (hm : Fits raw10Remainder[27]! m)
    (hd0 : m (3,false) = decode 14) (hd1 : m (3,true) = decode 17)
    (he : m (4,false) = decode e) : compatible (table e) m := by
  have e0 : raw10Remainder[27]! (0,false) = [decode 8] := by decide
  have e1 : raw10Remainder[27]! (1,false) = [decode 11] := by decide
  have e2 : raw10Remainder[27]! (2,false) = [decode 13] := by decide
  have e3 : raw10Remainder[27]! (2,true) = [decode 13] := by decide
  have h0 : m (0,false) = decode 8 := by simpa [e0] using hm (0,false)
  have h1 : m (1,false) = decode 11 := by simpa [e1] using hm (1,false)
  have h2 : m (2,false) = decode 13 := by simpa [e2] using hm (2,false)
  have h3 : m (2,true) = decode 13 := by simpa [e3] using hm (2,true)
  intro s t ht
  obtain ⟨q,b⟩ := s
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;>
    cases b <;> simp [table] at ht ⊢ <;> simp_all

theorem source_bound (m : Machine)
    (hm : Fits raw10Remainder[27]! m)
    (hd0 : m (3,false) = decode 14) (hd1 : m (3,true) = decode 17)
    (he : ∃ e : Fin 25, e ∈ easy ∧ m (4,false) = decode e) :
    WeightedBound 108 m := by
  obtain ⟨e,he,hval⟩ := he
  exact bound e he m (from_source e m hm hd0 hd1 hval)

#print axioms checks
#print axioms bound
#print axioms source_bound
end BB6.Agent49.Box27EasyE0
