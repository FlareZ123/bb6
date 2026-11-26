import Raw122Base
import LateCheck0
import LateCheck1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122Sharp
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
open BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit BB6Coverage.Agent10ZipAudit
abbrev late0 := BB6Coverage.Agent29PackedLate.M0.table
abbrev late1 := BB6Coverage.Agent29PackedLate.M1.table

theorem late0_read : zipRead late0 6659486 = some (0,true) :=
  packed_read (p:=late0) (n:=6659486) (z:=BB6Coverage.Agent29PackedLate.M0.e306) BB6Coverage.Agent29PackedLate.M0.exact_run

theorem late1_read : zipRead late1 1296924 = some (1,true) :=
  packed_read (p:=late1) (n:=1296924) (z:=BB6Coverage.Agent29PackedLate.M1.e88) BB6Coverage.Agent29PackedLate.M1.exact_run

theorem late0_delays : possibleDelays late0 0 = [0] := by decide
theorem late1_delays : possibleDelays late1 0 = [0,1] := by decide

theorem late0_check : zipCheck 6659487 late0 (.last 6659486 (0,true)) = true := by
  rw [zipCheck.eq_1]
  simp only [zipQueryOK,late0_read]
  decide

theorem late1_check : zipCheck 1296926 late1 (.last 1296924 (1,true)) = true := by
  rw [zipCheck.eq_1]
  simp only [zipQueryOK,late1_read]
  decide

theorem late0_bound (m : Machine) (hm : compatible late0 m) : WeightedBound 6659487 m := by
  have h : partialCheck 6659487 late0 (.closed (.last 6659486 (0,true))) = true := late0_check
  have hn : weightedTNFNoAssignedHalt late0 := by
    intro ⟨q,b⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide
  rcases partialSound 6659487 late0 (.closed (.last 6659486 (0,true))) (by decide) hn h m hm with h|⟨e,he,_⟩
  · exact h
  · simp [partialResiduals] at he

theorem late1_bound (m : Machine) (hm : compatible late1 m) : WeightedBound 1296926 m := by
  have h : partialCheck 1296926 late1 (.closed (.last 1296924 (1,true))) = true := late1_check
  have hn : weightedTNFNoAssignedHalt late1 := by
    intro ⟨q,b⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide
  rcases partialSound 1296926 late1 (.closed (.last 1296924 (1,true))) (by decide) hn h m hm with h|⟨e,he,_⟩
  · exact h
  · simp [partialResiduals] at he

def longest : Machine := fun s => (late0 s).getD none

theorem longest_compatible : compatible late0 longest := by
  intro s t h
  simp [longest,h]

theorem longest_parent_compatible : compatible BB6.Agent43Raw122.parent longest := by
  intro s t h
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> first | contradiction | (cases h; rfl)

theorem longest_halts : HaltsAfter longest 6659486 := by
  have hread := late0_read
  rw [zipRead_eq] at hread
  cases hr : knownRun late0 6659486 with
  | none => simp [hr] at hread
  | some c =>
    have hs : readSlot c = (0,true) := by simpa [hr] using hread
    have hrun := knownRun_sound late0 longest longest_compatible 6659486 c hr
    constructor
    · change (run longest 6659486 blank).isSome = true
      rw [hrun]
      rfl
    · rw [run,hrun]
      have hh : longest (0,true) = none := by decide
      simp [rawStep,hs,hh]

theorem longest_delay : 0 ∈ delays (zeroNext longest) 0 := by decide

theorem lower (B : Nat) (h : ∀ m, compatible BB6.Agent43Raw122.parent m → WeightedBound B m) : 6659487 ≤ B :=
  h longest longest_parent_compatible 6659486 0 longest_halts longest_delay
#print axioms late0_bound
#print axioms late1_bound
#print axioms longest_halts
#print axioms lower
end BB6.Agent43Raw122Sharp
