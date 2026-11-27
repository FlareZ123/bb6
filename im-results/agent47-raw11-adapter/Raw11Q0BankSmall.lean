import Raw11Q0BankSmallPart0
import Raw11Q0BankSmallPart1
import Raw11Q0FreshClosed

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw11Q0BankSmall
open BB6Coverage BB6.Agent13BlankDelay

def closedParents : List PartialMachine := [p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p29,p31,p32,p36,p38,p40,p42,p43,p54,p59,p61,p63,p65,p67,p69,p71,p79,p84,p96,p97,p99,p100,p101,p103,p104,p105,p107,p109,p111,p116,p117,p119,p123,p124,p125]

theorem covers (B : Nat) (hB : 100 ≤ B) : ∀ p ∈ closedParents, Cover (WeightedBound B) p := by
  intro p hp
  simp only [closedParents,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact Q0RosterConsume.liftCover hB cover_p0
  · exact Q0RosterConsume.liftCover hB cover_p1
  · exact Q0RosterConsume.liftCover hB cover_p2
  · exact Q0RosterConsume.liftCover hB cover_p3
  · exact Q0RosterConsume.liftCover hB cover_p4
  · exact Q0RosterConsume.liftCover hB cover_p5
  · exact Q0RosterConsume.liftCover hB cover_p6
  · exact Q0RosterConsume.liftCover hB cover_p7
  · exact Q0RosterConsume.liftCover hB cover_p8
  · exact Q0RosterConsume.liftCover hB cover_p9
  · exact Q0RosterConsume.liftCover hB cover_p10
  · exact Q0RosterConsume.liftCover hB cover_p11
  · exact Q0RosterConsume.liftCover hB cover_p12
  · exact Q0RosterConsume.liftCover hB cover_p13
  · exact Q0RosterConsume.liftCover hB cover_p14
  · exact Q0RosterConsume.liftCover hB cover_p15
  · exact Q0RosterConsume.liftCover hB cover_p16
  · exact Q0RosterConsume.liftCover hB cover_p17
  · exact Q0RosterConsume.liftCover hB cover_p18
  · exact Q0RosterConsume.liftCover hB cover_p19
  · exact Q0RosterConsume.liftCover hB cover_p20
  · exact Q0RosterConsume.liftCover hB cover_p21
  · exact Q0RosterConsume.liftCover hB cover_p22
  · exact Q0RosterConsume.liftCover hB cover_p23
  · exact Q0RosterConsume.liftCover hB cover_p24
  · exact Q0RosterConsume.liftCover hB cover_p29
  · exact Q0RosterConsume.liftCover hB cover_p31
  · exact Q0RosterConsume.liftCover hB cover_p32
  · exact Q0RosterConsume.liftCover hB cover_p36
  · exact Q0RosterConsume.liftCover hB cover_p38
  · exact Q0RosterConsume.liftCover hB cover_p40
  · exact Q0RosterConsume.liftCover hB cover_p42
  · exact Q0RosterConsume.liftCover hB cover_p43
  · exact Q0RosterConsume.liftCover hB cover_p54
  · exact Q0RosterConsume.liftCover hB cover_p59
  · exact Q0RosterConsume.liftCover hB cover_p61
  · exact Q0RosterConsume.liftCover hB cover_p63
  · exact Q0RosterConsume.liftCover hB cover_p65
  · exact Q0RosterConsume.liftCover hB cover_p67
  · exact Q0RosterConsume.liftCover hB cover_p69
  · exact Q0RosterConsume.liftCover hB cover_p71
  · exact Q0RosterConsume.liftCover hB cover_p79
  · exact Q0RosterConsume.liftCover hB cover_p84
  · exact Q0RosterConsume.liftCover hB cover_p96
  · exact Q0RosterConsume.liftCover hB cover_p97
  · exact Q0RosterConsume.liftCover hB cover_p99
  · exact Q0RosterConsume.liftCover hB cover_p100
  · exact Q0RosterConsume.liftCover hB cover_p101
  · exact Q0RosterConsume.liftCover hB cover_p103
  · exact Q0RosterConsume.liftCover hB cover_p104
  · exact Q0RosterConsume.liftCover hB cover_p105
  · exact Q0RosterConsume.liftCover hB cover_p107
  · exact Q0RosterConsume.liftCover hB cover_p109
  · exact Q0RosterConsume.liftCover hB cover_p111
  · exact Q0RosterConsume.liftCover hB cover_p116
  · exact Q0RosterConsume.liftCover hB cover_p117
  · exact Q0RosterConsume.liftCover hB cover_p119
  · exact Q0RosterConsume.liftCover hB cover_p123
  · exact Q0RosterConsume.liftCover hB cover_p124
  · exact Q0RosterConsume.liftCover hB cover_p125

def closedCodes : List Nat := closedParents.map BB6.Agent47PhaseFrontier.tableCode
def remaining : List PartialMachine := Q0RosterConsume.removeCovered BB6.Agent47Raw11Q0FreshClosed.remaining closedParents
theorem closed_codes_nodup : closedCodes.Nodup := by decide +kernel
theorem closed_codes_in_remaining : ∀ c ∈ closedCodes, c ∈ BB6.Agent47Raw11Q0FreshClosed.remaining.map BB6.Agent47PhaseFrontier.tableCode := by decide +kernel
theorem remaining_exact : remaining.map BB6.Agent47PhaseFrontier.tableCode =
    (BB6.Agent47Raw11Q0FreshClosed.remaining.map BB6.Agent47PhaseFrontier.tableCode).filter (fun c => !(closedCodes.contains c)) := by decide +kernel
theorem remaining_census : (BB6.Agent47Raw11Route.fullRoster.length, remaining.length) = (299,167) := by decide +kernel
theorem cover_from_remaining (B : Nat) (hB : 4663 ≤ B)
    (h : ∀ p ∈ remaining, ∀ m, compatible p m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent47Raw11Route.parent := by
  exact BB6.Agent47Raw11Q0FreshClosed.cover_from_remaining B hB
    (Q0RosterConsume.consume B BB6.Agent47Raw11Q0FreshClosed.remaining closedParents
      (covers B (Nat.le_trans (by decide : 100 ≤ 4663) hB)) h)

#print axioms covers
#print axioms closed_codes_in_remaining
#print axioms remaining_exact
#print axioms remaining_census
#print axioms cover_from_remaining
end BB6.Agent47Raw11Q0BankSmall
