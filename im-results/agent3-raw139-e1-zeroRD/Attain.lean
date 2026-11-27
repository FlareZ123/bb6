import PackedAudit
import FastThreeHoleAudit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent3Raw139E1ZeroRDD0ZeroRE
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10FastAudit BB6Coverage.Agent10ZipAudit BB6.Agent3PackedAudit

def targetParent : PartialMachine := fromCodes [7,24,11,24,14,24,17,16,24,13,24,24]
def late : PartialMachine := fromCodes [7,20,11,5,14,11,17,16,2,13,11,24]
def witness : Machine := fun s => (late s).getD none

theorem fits : compatible targetParent witness := by
  intro s t h
  rcases s with ⟨q,b⟩
  have hh : ∀ q : Fin 6, ∀ b : Bool, ∀ t : Transition, targetParent (q,b) = some t → witness (q,b) = t := by decide +kernel
  exact hh q b t h

theorem query527 : packedQueryOK 528 late 527 (5,true) = true := by decide +kernel

theorem halt527 : HaltsAfter witness 527 := by
  obtain ⟨hread, hhole, hw⟩ := packedQueryOK_sound query527
  cases hr : knownRun late 527 with
  | none => simp [hr] at hread
  | some c =>
    have hs : readSlot c = (5,true) := by simpa [hr] using hread
    apply first_hole_halts late 527 c hr (by rw [hs]; exact hhole)
    rw [hs]
    intro s t h
    by_cases he : s = (5,true)
    · subst s
      have ht : t = none := by simpa [refine] using h.symm
      subst t
      simp [witness, hhole]
    · have ht : late s = some t := by simpa [refine,he] using h
      simp [witness, ht]

theorem delayZero : 0 ∈ delays (zeroNext witness) 0 := by decide +kernel
theorem lower (B : Nat) (h : ∀ m, compatible targetParent m → WeightedBound B m) : 528 ≤ B :=
  h witness fits 527 0 halt527 delayZero
#print axioms lower
end BB6.Agent3Raw139E1ZeroRDD0ZeroRE
