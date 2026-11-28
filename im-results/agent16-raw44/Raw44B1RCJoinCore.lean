import ZipThreeHoleAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent16Raw44B1RCJoin
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent10ZipAudit BB6.Agent31ThreeHole

def parent : PartialMachine := fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,false,1⟩)
  | _, _ => none

def slot : Slot := (2,true)
def child (t : Transition) : PartialMachine := refine parent slot t

theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem parent_hole : parent slot = none := by decide

#eval possibleDelays (child none) 0

theorem halt_checked : zipQueryOK 10 parent 7 slot = true := by decide +kernel

theorem halt_bound (m : Machine) (hm : compatible (child none) m) : WeightedBound 10 m := by
  obtain ⟨hread, hhole, hw⟩ := zipQueryOK_sound halt_checked
  cases hr : knownRun parent 7 with
  | none => simp [hr] at hread
  | some c =>
    have hs : readSlot c = slot := by simpa [hr] using hread
    exact first_hole_weighted_halt 10 parent 7 c parent_root hr
      (by simpa [hs] using hhole)
      (by simpa [hs] using BB6.Agent50TNFPilot.weightOK_sound parent slot 7 10 hw)
      m (by simpa [child,hs] using hm)

theorem weighted_mono {A B : Nat} (h : A ≤ B) {m : Machine} (ha : WeightedBound A m) :
    WeightedBound B m := fun k d hk hd => Nat.le_trans (ha k d hk hd) h

/-- Exact physical branch join. The genuine halt outcome has a direct proof. -/
theorem join (B : Nat) (hB : 10 ≤ B)
    (ordinary : ∀ mv : Move, ∀ m : Machine, compatible (child (some mv)) m → WeightedBound B m) :
    Cover (WeightedBound B) parent := by
  apply Cover.branch parent slot parent_hole
  intro t _
  cases t with
  | none => exact Cover.leaf _ (fun m hm => weighted_mono hB (halt_bound m hm))
  | some mv => exact Cover.leaf _ (ordinary mv)

#print axioms halt_bound
#print axioms join
end BB6.Agent16Raw44B1RCJoin
