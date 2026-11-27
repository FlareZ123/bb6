import Box27GrowingBlock
import Box33SourceBridge
import WeightedTNF
import Raw10EncodedSourceBridge
import Box17AuditCore

namespace BB6.Agent49.Box27GrowingBlockSource
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent13.Box17 (decode)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

abbrev project := BB6.Agent13.Box33Source.project false

-- E1 and F1 are absent, not asserted to be halt transitions.
def partial : PartialMachine := fun s =>
  match s with
  | (0,false) => some (decode 8)
  | (0,true) => some (decode 3)
  | (1,false) => some (decode 11)
  | (1,true) => some (decode 2)
  | (2,false) => some (decode 13)
  | (2,true) => some (decode 13)
  | (3,false) => some (decode 14)
  | (3,true) => some (decode 17)
  | (4,false) => some (decode 21)
  | (5,false) => some (decode 3)
  | _ => none

theorem map_knownStep (z : Config) :
    (knownStep partial z).map project = Box27GrowingBlock.step (project z) := by
  rcases z with ⟨s,h,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t h <;>
    simp [knownStep,readSlot,partial,decode,hb]
  all_goals try rw [BB6.Agent13.Box33Source.project_applyMove]
  all_goals simp [Box27GrowingBlock.step,project,BB6.Agent13.Box33Source.project,
    BB6.Agent13.Box33Source.q,BB6.Agent13.Box33Source.perm,hb]

theorem map_knownRun (n : Nat) :
    (knownRun partial n).map project = Box27GrowingBlock.run n Box27GrowingBlock.blank := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Box27GrowingBlock.run_add n 1,← ih]
    simp only [knownRun]
    cases h : knownRun partial n with
    | none => rfl
    | some z =>
      simp only [Option.bind_some,Option.map_some]
      rw [map_knownStep]
      simp [Box27GrowingBlock.run]

theorem compatible_never (m : Machine) (hm : compatible partial m) : NeverHalts m := by
  intro n
  have h := map_knownRun n
  cases he : knownRun partial n with
  | none => exact False.elim (Box27GrowingBlock.never_blank n (by simpa [he] using h.symm))
  | some c =>
    rw [knownRun_sound partial m hm n c he]
    rfl

theorem parent_rows (m : Machine) (hm : Fits raw10Remainder[27]! m) :
    m (0,false) = decode 8 ∧ m (1,false) = decode 11 ∧
    m (2,false) = decode 13 ∧ m (2,true) = decode 13 := by
  have e0 : raw10Remainder[27]! (0,false) = [decode 8] := by decide
  have e1 : raw10Remainder[27]! (1,false) = [decode 11] := by decide
  have e2 : raw10Remainder[27]! (2,false) = [decode 13] := by decide
  have e3 : raw10Remainder[27]! (2,true) = [decode 13] := by decide
  exact ⟨by simpa [e0] using hm (0,false),by simpa [e1] using hm (1,false),
    by simpa [e2] using hm (2,false),by simpa [e3] using hm (2,true)⟩

theorem parent_never (m : Machine) (hm : Fits raw10Remainder[27]! m)
    (ha : m (0,true) = decode 3) (hb : m (1,true) = decode 2)
    (hd0 : m (3,false) = decode 14) (hd1 : m (3,true) = decode 17)
    (he : m (4,false) = decode 21) (hf : m (5,false) = decode 3) :
    NeverHalts m := by
  apply compatible_never m
  obtain ⟨h0,h1,h2,h3⟩ := parent_rows m hm
  intro s t ht
  obtain ⟨q,b⟩ := s
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;>
    simp [partial] at ht ⊢ <;> simp_all

theorem parent_bound (B : Nat) (m : Machine) (hm : Fits raw10Remainder[27]! m)
    (ha : m (0,true) = decode 3) (hb : m (1,true) = decode 2)
    (hd0 : m (3,false) = decode 14) (hd1 : m (3,true) = decode 17)
    (he : m (4,false) = decode 21) (hf : m (5,false) = decode 3) :
    WeightedBound B m :=
  weighted_never B m (parent_never m hm ha hb hd0 hd1 he hf)

#print axioms compatible_never
#print axioms parent_never
#print axioms parent_bound
end BB6.Agent49.Box27GrowingBlockSource
