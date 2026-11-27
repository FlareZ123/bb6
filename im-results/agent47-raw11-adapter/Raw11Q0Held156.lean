import Q00000SourceConsumer
import Raw11Root52CappedParentsConsume

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47Raw11Q0Held156
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent47PhaseFrontier (tableCode)

def parent : PartialMachine := BB6Generated.Q00000.sourceTable

theorem never (m : Machine) (hm : compatible parent m) : NeverHalts m :=
  BB6Generated.Q00000.source_never m hm

theorem cover (B : Nat) : Cover (WeightedBound B) parent :=
  .leaf _ fun m hm => weighted_never B m (never m hm)

theorem code_exact : tableCode parent = 27872153587416843 := by decide +kernel

theorem exact_literal : parent = (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none) := by
  funext s
  rcases s with ⟨q,b⟩
  have h : ∀ q : Fin 6, ∀ b : Bool, parent (q,b) =
      (match q.val,b with
      | 0,false => some (some ⟨true,true,1⟩)
      | 0,true => some (some ⟨true,true,3⟩)
      | 1,false => some (some ⟨true,true,2⟩)
      | 1,true => some (some ⟨false,false,3⟩)
      | 2,false => some (some ⟨false,false,0⟩)
      | 2,true => some (some ⟨false,true,4⟩)
      | 3,false => some (some ⟨true,false,0⟩)
      | 3,true => some (some ⟨true,false,1⟩)
      | 4,false => some (some ⟨false,true,5⟩)
      | 5,false => some (some ⟨false,false,0⟩)
      | 5,true => some (some ⟨true,true,0⟩)
      | _,_ => none) := by decide
  exact h q b

theorem held_count_in_237 :
    (BB6.Agent47Raw11Root52CappedParentsConsume.remaining.map tableCode).count (tableCode parent) = 1 := by decide +kernel

def remove (frontier : List PartialMachine) := Q0RosterConsume.removeCovered frontier [parent]

theorem discharge (B : Nat) (frontier : List PartialMachine)
    (h : ∀ p ∈ remove frontier, ∀ m, compatible p m → WeightedBound B m) :
    ∀ p ∈ frontier, ∀ m, compatible p m → WeightedBound B m := by
  apply Q0RosterConsume.consume B frontier [parent] _ h
  intro p hp
  simp at hp
  subst p
  exact cover B

def remaining : List PartialMachine := remove BB6.Agent47Raw11Root52CappedParentsConsume.remaining

theorem remaining_census : (BB6.Agent47Raw11Route.fullRoster.length, remaining.length) = (299,236) := by decide +kernel

theorem cover_from_remaining (B : Nat) (hB : 4663 ≤ B)
    (h : ∀ p ∈ remaining, ∀ m, compatible p m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent47Raw11Route.parent :=
  BB6.Agent47Raw11Root52CappedParentsConsume.cover_from_remaining B hB (discharge B _ h)

#print axioms remaining_census
#print axioms cover_from_remaining
#print axioms exact_literal
#print axioms code_exact
#print axioms held_count_in_237
#print axioms discharge

#print axioms never
#print axioms cover
end BB6.Agent47Raw11Q0Held156
