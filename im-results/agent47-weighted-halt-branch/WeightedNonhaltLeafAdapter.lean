import WeightedTNFCertificate

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace BB6.Agent47WeightedHalt

open BB6Coverage
open BB6.Agent13BlankDelay

/-- Forget every halting row of a complete machine, but retain every ordinary
    row. The canonical completion of this partial table is exactly the
    original machine. -/
def forgetHaltRows (m : Machine) : PartialMachine := fun s =>
  match m s with
  | none => none
  | some mv => some (some mv)

theorem forgetHaltRows_defaultCompletion (m : Machine) :
    weightedTNFDefaultCompletion (forgetHaltRows m) = m := by
  funext s
  cases h : m s <;> simp [weightedTNFDefaultCompletion, forgetHaltRows, h]

theorem forgetHaltRows_root (m : Machine)
    (hroot : m initialSlot = some ⟨true, true, 1⟩) :
    forgetHaltRows m initialSlot = some (some ⟨true, true, 1⟩) := by
  simp [forgetHaltRows, hroot]

theorem forgetHaltRows_tnfSupport (m : Machine) :
    TNFSupport (forgetHaltRows m) 6 := by
  intro s t _hs
  constructor
  · exact s.1.isLt
  · intro mv _hm
    exact mv.next.isLt

theorem forgetHaltRows_noAssignedHalt (m : Machine) :
    weightedTNFNoAssignedHalt (forgetHaltRows m) := by
  intro s
  cases h : m s <;> simp [forgetHaltRows, h]

/-- If the original complete machine never halts, then the partial table
    obtained by forgetting its halt rows has an infinite known run. Its
    default completion is the original machine, so the known-run theorem
    upgrades this to nonhalting of every compatible completion. -/
theorem forgetHaltRows_all_completions_neverHalt (m : Machine)
    (hnever : NeverHalts m) :
    ∀ m', compatible (forgetHaltRows m) m' → NeverHalts m' := by
  have hforever : weightedTNFKnownRunForever (forgetHaltRows m) := by
    intro n
    rw [weightedTNFKnownRun_eq_defaultRun (forgetHaltRows m) n,
      forgetHaltRows_defaultCompletion]
    cases hrun : run m n blank with
    | none =>
        have hsome := hnever n
        simp [hrun] at hsome
    | some c => exact ⟨c, rfl⟩
  exact (weightedTNFKnownRunForever_iff (forgetHaltRows m)).mp hforever

/-- Any complete nonhalting machine already in the 1RB root cylinder yields
    a source-independent weighted-TNF nonhalt leaf, even if its literal
    table contains unreachable halt rows. -/
def forgetHaltRows_nonhaltCertificate (B : Nat) (m : Machine)
    (hroot : m initialSlot = some ⟨true, true, 1⟩)
    (hnever : NeverHalts m) :
    WeightedTNFCertificate B (forgetHaltRows m) 6 :=
  .nonhalt
    (forgetHaltRows_root m hroot)
    (forgetHaltRows_tnfSupport m)
    (forgetHaltRows_noAssignedHalt m)
    (forgetHaltRows_all_completions_neverHalt m hnever)

/-- Cover form of the same adapter, useful before constructing a larger
    certificate tree. -/
theorem forgetHaltRows_nonhaltCover (m : Machine) (hnever : NeverHalts m) :
    Cover NeverHalts (forgetHaltRows m) :=
  .leaf (forgetHaltRows m)
    (forgetHaltRows_all_completions_neverHalt m hnever)

#print axioms forgetHaltRows_defaultCompletion
#print axioms forgetHaltRows_root
#print axioms forgetHaltRows_tnfSupport
#print axioms forgetHaltRows_noAssignedHalt
#print axioms forgetHaltRows_all_completions_neverHalt
#print axioms forgetHaltRows_nonhaltCertificate
#print axioms forgetHaltRows_nonhaltCover

end BB6.Agent47WeightedHalt
