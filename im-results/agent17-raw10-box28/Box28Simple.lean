import Box17AuditCore
import Raw10EncodedSourceBridge

namespace BB6.Agent17.Box28Simple
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent13.Box17 (decode slot index leafCheck leafCheck_sound Witness)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def cylinder (d0 : Fin 25) (d1 : Option (Fin 25)) : PartialMachine := fun s =>
  match s with
  | (0,false) => some (decode 8)
  | (1,false) => some (decode 11)
  | (2,false) => some (decode 11)
  | (2,true) => some (decode 13)
  | (3,false) => some (decode d0)
  | (3,true) => d1.map decode
  | _ => none

def firstWitness (d0 : Fin 25) : Option Witness :=
  match d0.val with
  | 0 => some (.halt 3)
  | 5 => some (.cycle 5 1 false (-3))
  | 6 => some (.cycle 5 1 false (-1))
  | 7 => some (.cycle 5 1 false (-3))
  | 9 => some (.cycle 4 1 false (-2))
  | 10 => some (.cycle 4 1 false 0)
  | 12 => some (.cycle 2 3 false 0)
  | _ => none

def secondWitness (d0 d1 : Fin 25) : Option Witness :=
  match d0.val,d1.val with
  | 14,0 => some (.halt 5)
  | 14,1 => some (.cycle 0 6 true (-1))
  | 14,2 => some (.cycle 0 6 true (-1))
  | 14,5 => some (.cycle 7 1 false (-1))
  | 14,6 => some (.cycle 7 1 false 1)
  | 14,7 => some (.cycle 7 1 false (-1))
  | 14,8 => some (.cycle 1 5 true (-1))
  | 14,9 => some (.cycle 6 1 false 0)
  | 14,10 => some (.cycle 6 1 false 2)
  | 14,11 => some (.cycle 6 1 false 0)
  | 14,12 => some (.cycle 2 5 true (-1))
  | 14,13 => some (.cycle 6 1 true 0)
  | 14,14 => some (.cycle 6 1 true 2)
  | 14,15 => some (.cycle 4 2 true 0)
  | 14,16 => some (.cycle 6 1 true 2)
  | 16,0 => some (.halt 5)
  | 16,2 => some (.cycle 0 6 true (-1))
  | 16,6 => some (.cycle 11 1 false (-1))
  | 16,9 => some (.cycle 8 1 false (-2))
  | 16,10 => some (.cycle 10 1 false 0)
  | 16,11 => some (.cycle 8 1 false (-2))
  | 16,12 => some (.cycle 5 13 false 2)
  | 16,13 => some (.cycle 8 1 true (-2))
  | 16,14 => some (.cycle 6 1 true 2)
  | 16,15 => some (.cycle 6 3 false 0)
  | 16,16 => some (.cycle 6 1 true 2)
  | _,_ => none

def accepted (p : PartialMachine) (w : Option Witness) : Bool :=
  match w with
  | none => true
  | some v => leafCheck 11 #[] p v

theorem first_checks : ∀ d0 : Fin 25,
    accepted (cylinder d0 none) (firstWitness d0) = true := by decide

theorem second_checks : ∀ d0 d1 : Fin 25,
    accepted (cylinder d0 (some d1)) (secondWitness d0 d1) = true := by decide

theorem witness_sound (p : PartialMachine) (w : Option Witness)
    (ha : accepted p w = true) (hw : w.isSome = true)
    (m : Machine) (hm : compatible p m) : WeightedBound 11 m := by
  cases h : w with
  | none => simp [h] at hw
  | some v =>
    apply leafCheck_sound 11 #[] ?_ p v (by simpa [accepted,h] using ha) m hm
    intro i q hi
    simp at hi

theorem first_bound (d0 : Fin 25) (m : Machine)
    (h : (firstWitness d0).isSome = true) (hm : compatible (cylinder d0 none) m) :
    WeightedBound 11 m :=
  witness_sound _ _ (first_checks d0) h m hm

theorem second_bound (d0 d1 : Fin 25) (m : Machine)
    (h : (secondWitness d0 d1).isSome = true)
    (hm : compatible (cylinder d0 (some d1)) m) : WeightedBound 11 m :=
  witness_sound _ _ (second_checks d0 d1) h m hm

-- Connect these cylinder proofs to the actual base34 source rectangle.
theorem parent_rows (m : Machine) (hm : Fits raw10Remainder[28]! m) :
    m (0,false) = decode 8 ∧ m (1,false) = decode 11 ∧
    m (2,false) = decode 11 ∧ m (2,true) = decode 13 := by
  have e0 : raw10Remainder[28]! (0,false) = [decode 8] := by decide
  have e1 : raw10Remainder[28]! (1,false) = [decode 11] := by decide
  have e2 : raw10Remainder[28]! (2,false) = [decode 11] := by decide
  have e3 : raw10Remainder[28]! (2,true) = [decode 13] := by decide
  exact ⟨by simpa [e0] using hm (0,false),by simpa [e1] using hm (1,false),
    by simpa [e2] using hm (2,false),by simpa [e3] using hm (2,true)⟩

theorem compatible_parent (m : Machine) (hm : Fits raw10Remainder[28]! m)
    (d0 : Fin 25) (d1 : Option (Fin 25))
    (h0 : m (3,false) = decode d0)
    (h1 : ∀ v, d1 = some v → m (3,true) = decode v) :
    compatible (cylinder d0 d1) m := by
  obtain ⟨ha,hb,hc,hd⟩ := parent_rows m hm
  intro s t ht
  obtain ⟨q,b⟩ := s
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;>
    cases d1 <;> simp [cylinder] at ht ⊢ <;> simp_all

theorem parent_first (m : Machine) (hm : Fits raw10Remainder[28]! m)
    (d0 : Fin 25) (h0 : m (3,false) = decode d0)
    (hw : (firstWitness d0).isSome = true) : WeightedBound 11 m :=
  first_bound d0 m hw (compatible_parent m hm d0 none h0 (by simp))

theorem parent_second (m : Machine) (hm : Fits raw10Remainder[28]! m)
    (d0 d1 : Fin 25) (h0 : m (3,false) = decode d0)
    (h1 : m (3,true) = decode d1)
    (hw : (secondWitness d0 d1).isSome = true) : WeightedBound 11 m :=
  second_bound d0 d1 m hw (compatible_parent m hm d0 (some d1) h0 (by intro v hv; cases hv; exact h1))

#print axioms parent_first
#print axioms parent_second
end BB6.Agent17.Box28Simple
