import TM63RawUpperInterface
import WeightedNonhaltLeafAdapter
import FirstHolePath

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent48ChampionCylinder
open BB6Coverage BB6Coverage.Agent48Champion BB6.Agent47WeightedHalt
open BB6Coverage.Agent48DirectRoot BB6ChampionArithmetic BB6.Agent13BlankDelay

/-- Close an exact last-hole cylinder without executing the canonical
    completion again. Useful when its halt time is astronomically large. -/
theorem lastHole_of_good {good : Machine → Prop} (m0 : Machine) (s : Slot)
    (hHalt : m0 s = none)
    (hRest : ∀ t, t ≠ s → ∃ mv, m0 t = some mv)
    (hGood : good m0)
    (hTotal : ∀ m, (∀ t, ∃ mv, m t = some mv) → good m) :
    Cover good (forgetHaltRows m0) := by
  apply Cover.leaf
  intro m hm
  cases hs : m s with
  | none =>
    have he : m = m0 := by
      funext t
      by_cases ht : t = s
      · subst t; exact hs.trans hHalt.symm
      · obtain ⟨v,hv⟩ := hRest t ht
        exact (hm t _ (by simp [forgetHaltRows,hv])).trans hv.symm
    rw [he]
    exact hGood
  | some v =>
    apply hTotal m
    intro t
    by_cases ht : t = s
    · subst t; exact ⟨v,hs⟩
    · obtain ⟨w,hw⟩ := hRest t ht
      exact ⟨w,hm t _ (by simp [forgetHaltRows,hw])⟩

def b1 : Slot := (1,true)
def a1 : Slot := (0,true)

theorem champion_one_hole : ∀ t, t ≠ b1 → ∃ mv, championTable t = some mv := by
  have h : ∀ q : Fin 6, ∀ b : Bool, (q,b) ≠ b1 → (championTable (q,b)).isSome = true := by decide
  intro t ht
  have hh := h t.1 t.2 ht
  cases he : championTable t with
  | none => simp [he] at hh
  | some mv => exact ⟨mv,rfl⟩

/-- All 25 canonical completions, including the exact champion and all
    24 ordinary B1 assignments, are safe at the attained score. -/
theorem champion_last_hole_cover :
    Cover (WeightedBound (proposedTM63Moves+7)) (forgetHaltRows championTable) :=
  lastHole_of_good championTable b1 (by decide) champion_one_hole
    champion_weighted_bound
    (fun m h => weighted_never _ m (all_ordinary_never m h))

def championFirstHoleSchedule : List (Nat × Slot) :=
  [(1,(1,false)), (2,(2,false)), (3,(3,true)), (4,(4,true)),
   (7,(4,false)), (8,(3,false)), (11,(2,true)), (12,(5,true)),
   (53,(5,false)), (213,(0,true))]

theorem champion_last_hole_reachable :
    BB6.Agent8TNFPath.FirstHolePath (forgetHaltRows championTable) 6 :=
  BB6.Agent8TNFPath.checked_from_root championTable championFirstHoleSchedule (by decide)

noncomputable def championLastHoleCertificate :
    WeightedTNFCertificate (proposedTM63Moves+7) (forgetHaltRows championTable) 6 :=
  .ofWeightedCover (forgetHaltRows_root _ (by decide))
    (forgetHaltRows_tnfSupport _) (forgetHaltRows_noAssignedHalt _)
    champion_last_hole_cover

#print axioms champion_last_hole_cover
#print axioms champion_last_hole_reachable
#print axioms championLastHoleCertificate
end BB6.Agent48ChampionCylinder
