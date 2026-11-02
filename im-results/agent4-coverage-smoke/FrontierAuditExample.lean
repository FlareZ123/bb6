import FrontierAudit
import Prune
namespace BB6Coverage
set_option maxRecDepth 3000

/-- A first authenticated finite frontier from the fully unknown machine.
Three of its 25 initial-transition cylinders have genuine all-time proofs:
immediate halt, blank right drift, and blank left drift. All 22 other
cylinders remain explicitly unresolved. -/
def threeKnownInitial (B : Nat) (hb : 1 ≤ B) :
    FrontierAudit (DecidedBelow B) emptyTable :=
  .branch emptyTable initialSlot rfl (fun t _ =>
    if ht : t = none then
      .certified _ (by simpa [ht, immediateHalt] using immediate_halt_leaf B hb)
    else if hr : t = some (blankDrift true) then
      .certified _ (by simpa [hr, driftLeaf] using driftLeaf_certificate true B)
    else if hl : t = some (blankDrift false) then
      .certified _ (by simpa [hl, driftLeaf] using driftLeaf_certificate false B)
    else .unresolved _)

/-- Exact full-table multiplicity of the three proved and 22 open children. -/
theorem threeKnownInitial_report :
    (threeKnownInitial 2 (by decide)).report =
      (3 * 25^11, 22 * 25^11) := by decide

theorem threeKnownInitial_partition_mass :
    (threeKnownInitial 2 (by decide)).report.1 +
    (threeKnownInitial 2 (by decide)).report.2 = 25^12 := by
  rw [threeKnownInitial_report]
  decide

theorem threeKnownInitial_open_iff (m : Machine) :
    (threeKnownInitial 2 (by decide)).open m ↔
      m initialSlot ≠ none ∧
      m initialSlot ≠ some (blankDrift true) ∧
      m initialSlot ≠ some (blankDrift false) := by
  by_cases h0 : m initialSlot = none
  · simp [threeKnownInitial, FrontierAudit.open, h0]
  · by_cases h1 : m initialSlot = some (blankDrift true)
    · simp [threeKnownInitial, FrontierAudit.open, h0, h1]
    · by_cases h2 : m initialSlot = some (blankDrift false)
      · have hdiff : blankDrift false ≠ blankDrift true := by decide
        simp [threeKnownInitial, FrontierAudit.open, h0, h1, h2, hdiff]
      · have hdiff : blankDrift false ≠ blankDrift true := by decide
        simp [threeKnownInitial, FrontierAudit.open, h0, h1, h2, hdiff]

theorem threeKnownInitial_sound (m : Machine) :
    DecidedBelow 2 m ∨
      (m initialSlot ≠ none ∧
       m initialSlot ≠ some (blankDrift true) ∧
       m initialSlot ≠ some (blankDrift false)) := by
  rcases (threeKnownInitial 2 (by decide)).exhaustive m (empty_compatible m) with hg | ho
  · exact Or.inl hg
  · exact Or.inr ((threeKnownInitial_open_iff m).mp ho)

#print axioms threeKnownInitial_report
#print axioms threeKnownInitial_partition_mass
#print axioms threeKnownInitial_open_iff
#print axioms threeKnownInitial_sound
end BB6Coverage
