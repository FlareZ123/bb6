import Window7General
import Window5BankDomainsCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Window7DomainAudit
open BB6Coverage BB6.Agent50Window7 BB6.Agent50Window5DomainAudit
open BB6.Agent50Window5Domains

/-!
Source-checks radius-three physical action domains, each derived from
an invariant on seven ACTUAL tape cells. The finite table is original
Raw34 A0,B0,C0,D0 fixed, all other eight physical slots use 25
distinct instructions including HALT. Every supported input window
and BOTH possible incoming bits must be accepted.
-/

def allowedSlot7 (bits : Nat) (slot : Nat) (act : Nat) : Bool :=
  let source := (variableSlots[slot]?).getD (0,false)
  let action : Option Move := (allMoves[act]?).getD none
  permitted7Bool (masked7 bits) source.1 source.2 action

def validateEntry7 (entry : Nat × List Nat) : Bool :=
  decide (entry.2.length = 8) &&
    (List.range 8).all (fun i =>
      (List.range 25).all (fun j =>
        (!((entry.2[i]?).getD 0).testBit j) ||
         allowedSlot7 entry.1 i j))

def rootGood7 (bits : Nat) : Bool :=
  decide (masked7 bits 0 false false false false false false false = true) &&
  permitted7Bool (masked7 bits) 0 false (some ⟨true,true,1⟩) &&
  permitted7Bool (masked7 bits) 1 false (some ⟨true,true,2⟩) &&
  permitted7Bool (masked7 bits) 2 false (some ⟨false,true,3⟩) &&
  permitted7Bool (masked7 bits) 3 false (some ⟨true,false,2⟩)

end BB6.Agent50Window7DomainAudit
