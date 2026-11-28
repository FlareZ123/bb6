import Window5Domains
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Window5DomainAudit
open BB6Coverage BB6.Agent50Window5 BB6.Agent50Window5Domains

/-!
Trusted finite action-domain audit for exact 25-symbol physical tape
tables. Every 25-bit slot mask is checked action by action against
the original-tape radius-two permitted predicate. Index order:
D1,C1,B1,A1,E0,E1,F0,F1. The physical action list starts at HALT.
-/

def variableSlots : List (Fin 6 × Bool) :=
  [(⟨3,by decide⟩,true),
   (⟨2,by decide⟩,true),
   (⟨1,by decide⟩,true),
   (⟨0,by decide⟩,true),
   (⟨4,by decide⟩,false),
   (⟨4,by decide⟩,true),
   (⟨5,by decide⟩,false),
   (⟨5,by decide⟩,true)]

def allowedSlot (bits : Nat) (slot : Nat) (act : Nat) : Bool :=
  let source := (variableSlots[slot]?).getD (0,false)
  let action : Option Move := (allMoves[act]?).getD none
  decide (Permitted (masked bits) source.1 source.2 action)

/-- Test every set bit in the physical domain against actual
permission for this row and five-cell predicate. A 0 bit forbids the
action, and does not require proving anything about it. -/
def validateEntry (entry : Nat × List Nat) : Bool :=
  decide (entry.2.length = 8) &&
    (List.range 8).all (fun i =>
      (List.range 25).all (fun j =>
        (!((entry.2[i]?).getD 0).testBit j) ||
           allowedSlot entry.1 i j))

theorem slots_count : variableSlots.length = 8 := by decide
theorem actions_count : allMoves.length = 25 := by decide

#print axioms slots_count
#print axioms actions_count
end BB6.Agent50Window5DomainAudit
