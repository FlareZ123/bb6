import ZipAuditCore
import WeightedFirstOneCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent13Raw10FixedLeaves
open BB6Coverage BB6.Agent13BlankDelay
open BB6Coverage.Agent50Zipper BB6Coverage.Agent31Pump BB6Coverage.Agent10ZipAudit

/-- The exact two-hole 24+14 lasso used by Agent50's rectangle consumer. -/
def cycleTable : PartialMachine := fun s =>
  if s = (0,false) then some (some ⟨true,true,1⟩)
  else if s = (0,true) then some (some ⟨false,true,3⟩)
  else if s = (1,false) then some (some ⟨true,false,2⟩)
  else if s = (1,true) then none
  else if s = (2,false) then some (some ⟨false,false,4⟩)
  else if s = (2,true) then some (some ⟨true,true,0⟩)
  else if s = (3,false) then some (some ⟨false,false,2⟩)
  else if s = (3,true) then some (some ⟨false,true,0⟩)
  else if s = (4,false) then some (some ⟨true,false,5⟩)
  else if s = (4,true) then some (some ⟨true,false,3⟩)
  else if s = (5,false) then some (some ⟨false,true,2⟩)
  else none

def cycleEntry : Z := ⟨3, 0, [false,false,true,true,false], [true,false,false]⟩

theorem cycle_entry : zrun cycleTable 24 start = some cycleEntry := by decide

theorem cycle_return : zrun cycleTable 14 cycleEntry = some cycleEntry := by decide

theorem cycle_checked : zipCycle cycleTable 24 14 true (-10) = true := by decide

theorem cycle_never (m : Machine) (hm : compatible cycleTable m) : NeverHalts m :=
  zipCycle_sound cycleTable 24 14 true (-10) (by decide) cycle_checked m hm

def haltTable : PartialMachine := fun s =>
  if s = (0,false) then some (some ⟨true,true,1⟩)
  else if s = (0,true) then some none
  else if s = (1,false) then some (some ⟨true,false,2⟩)
  else if s = (2,true) then some none
  else none

def haltEntry : Z := ⟨2, 0, [true], [true]⟩

theorem halt_entry : zrun haltTable 2 start = some haltEntry := by decide

theorem halt_query : haltTable (haltEntry.q, haltEntry.l.headD false) = some none := by decide

theorem halt_exact (m : Machine) (hm : compatible haltTable m) : HaltsAfter m 2 := by
  have h2 := zrun_sound haltTable m hm 2 start haltEntry halt_entry
  rw [start_embed] at h2
  have hstep : rawStep m (embed haltEntry) = none := by
    rw [rawStep, read_embed, hm _ _ halt_query]
    rfl
  constructor
  · rw [h2]; rfl
  · rw [run, h2]; exact hstep

theorem halt_root : haltTable initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem halt_delay_bound : ∀ d ∈ possibleDelays haltTable 0, d + 2 + 1 ≤ 8 := by
  intro d hd
  have hmem : d ∈ List.range 6 := (List.mem_filter.mp hd).1
  have hlt : d < 6 := List.mem_range.mp hmem
  omega

theorem halt_cover : Cover (WeightedBound 8) haltTable :=
  weighted_halt_leaf haltTable 8 2 halt_root halt_exact halt_delay_bound

theorem cycle_cover (B : Nat) : Cover (WeightedBound B) cycleTable :=
  Cover.leaf _ (fun m hm => weighted_of_never B m (cycle_never m hm))

theorem holes_exact : ∀ s, cycleTable s = none ↔ s = (1,true) ∨ s = (5,true) := by
  rintro ⟨q,a⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> cases a <;> decide

theorem cycle_root : cycleTable initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem support : TNFSupport cycleTable 6 := by
  intro s t hs
  exact ⟨s.1.isLt, fun mv hm => mv.next.isLt⟩

theorem no_assigned_halt : weightedTNFNoAssignedHalt cycleTable := by
  unfold weightedTNFNoAssignedHalt
  rintro ⟨q,a⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> cases a <;> decide

theorem exactly_four_assigned : ∀ s, haltTable s ≠ none ↔
  s = (0,false) ∨ s = (0,true) ∨ s = (1,false) ∨ s = (2,true) := by
  rintro ⟨q,a⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> cases a <;> decide

def certificate (B : Nat) : WeightedTNFCertificate B cycleTable 6 :=
  .nonhalt cycle_root support no_assigned_halt cycle_never

#print axioms cycle_entry
#print axioms cycle_return
#print axioms cycle_never
#print axioms halt_exact
#print axioms halt_cover
#print axioms cycle_cover
#print axioms certificate

end BB6.Agent13Raw10FixedLeaves
