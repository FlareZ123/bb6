import Canonical68StableBatch
import Raw60RootFull
import Raw109Closed
import Raw110ParentLateCover
import Raw111Data
import Raw117Data
import Raw121Data
import Raw123ResidualClosure
import Raw125ResidualClosure

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31Canonical68Integrated
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent47CanonicalFrontier BB6.Agent31FourHoleRoster
open BB6.Agent31StableParentBatch

/-- Exact identity of each selected parent with its independently proved table. -/
theorem p109_eq : p109 = BB6.Agent4Raw109Cut.parent := by
  first | rfl | exact sameTable_sound (by decide)
theorem p123_eq : p123 = BB6.Agent7Raw123.p123 := by
  first | rfl | exact sameTable_sound (by decide)
theorem p60_eq : p60 = BB6.Agent1Raw60Root.parent := by
  first | rfl | exact sameTable_sound (by decide)
theorem p110_eq : p110 = BB6.Agent7Raw110.p110 := by
  first | rfl | exact sameTable_sound (by decide)
theorem p111_eq : p111 = BB6.Agent47Raw111.parent := by
  first | rfl | exact sameTable_sound (by decide)
theorem p117_eq : p117 = BB6.Agent8Raw117.p117 := by
  first | rfl | exact sameTable_sound (by decide)
theorem p121_eq : p121 = BB6.Agent11Raw121.p121 := by
  first | rfl | exact sameTable_sound (by decide)
theorem p125_eq : p125 = BB6.Agent13Raw125.p125 := by
  first | rfl | exact sameTable_sound (by decide)

theorem cover109 : Cover (WeightedBound 1703) p109 := by
  rw [p109_eq]
  exact Cover.leaf _ BB6.Agent4Raw109Closed.all_closed

theorem cover123 : Cover (WeightedBound 10000) p123 := by
  rw [p123_eq]
  exact BB6.Agent7Raw123.raw123_cover 10000 (by decide)

theorem cover60 : Cover (WeightedBound 1175) p60 := by
  rw [p60_eq]
  exact Cover.leaf _ BB6.Agent1Raw60Root.all60

theorem cover110 : Cover (WeightedBound 6766859) p110 := by
  rw [p110_eq]
  exact BB6.Agent7Raw110.raw110_cover 6766859 (by decide)

theorem cover111 : Cover (WeightedBound 7014) p111 := by
  rw [p111_eq]
  exact Cover.leaf _ BB6.Agent47Raw111.all_completions

theorem cover117 : Cover (WeightedBound 1291) p117 := by
  rw [p117_eq]
  exact Cover.leaf _ BB6.Agent8Raw117.all117

theorem cover121 : Cover (WeightedBound 4063) p121 := by
  rw [p121_eq]
  exact Cover.leaf _ BB6.Agent11Raw121.all121

theorem cover125 : Cover (WeightedBound 1290) p125 := by
  rw [p125_eq]
  exact BB6.Agent13Raw125.raw125_cover 1290 (by decide)

theorem all_parents : ∀ p ∈ parents, Cover (WeightedBound 6766859) p := by
  intro p hp
  simp only [parents, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact liftCover (by decide) cover60
  · exact liftCover (by decide) cover109
  · exact cover110
  · exact liftCover (by decide) cover111
  · exact liftCover (by decide) cover117
  · exact liftCover (by decide) cover121
  · exact liftCover (by decide) cover123
  · exact liftCover (by decide) cover125

/-- All eight parent premises are discharged by named source theorems.
The residual roster itself remains an explicit proof obligation. -/
theorem sound68_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster68, TNFQuotientCompatible e.2 m :=
  sound68 (by decide) all_parents

theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster68, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound68_integrated hLeaves champ

#print axioms p109_eq
#print axioms p123_eq
#print axioms cover109
#print axioms cover123
#print axioms all_parents
#print axioms p60_eq
#print axioms p110_eq
#print axioms p111_eq
#print axioms p117_eq
#print axioms p121_eq
#print axioms p125_eq
#print axioms cover60
#print axioms cover110
#print axioms cover111
#print axioms cover117
#print axioms cover121
#print axioms cover125
#print axioms sound68_integrated
#print axioms exact_at_target

end BB6.Agent31Canonical68Integrated
