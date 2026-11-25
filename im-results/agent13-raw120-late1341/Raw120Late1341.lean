import Late1341Trace
import ZipThreeHoleAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent13Raw120Late1341
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31ThreeHole BB6.Agent10ZipAudit

theorem delays_exact : possibleDelays (refine table (0,true) none) 0 = [0,1] := by decide

theorem weight_checked (B : Nat) (hB : 224707 ≤ B) :
    weightOK table (0,true) 224705 B = true := by
  unfold weightOK
  rw [delays_exact]
  apply List.all_eq_true.mpr
  intro d hd
  simp at hd
  rcases hd with rfl | rfl <;> exact decide_eq_true (by omega)

theorem lateQueryOK (B : Nat) (hB : 224707 ≤ B) :
    zipQueryOK B table 224705 (0,true) = true := by
  unfold zipQueryOK
  rw [query,weight_checked B hB]
  decide

theorem lateChecked (B : Nat) (hB : 224707 ≤ B) :
    zipCheck B table (.last 224705 (0,true)) = true := by
  simp only [zipCheck,lateQueryOK B hB,Bool.true_and]
  decide

theorem exact_halt (m : Machine) (hm : compatible (refine table (0,true) none) m) :
    HaltsAfter m 224705 := by
  obtain ⟨hr,hh,_⟩ := zipQueryOK_sound (lateQueryOK 224707 (by decide))
  cases hrun : knownRun table 224705 with
  | none => simp [hrun] at hr
  | some c =>
    have hs : readSlot c = (0,true) := by simpa [hrun] using hr
    exact first_hole_halts table 224705 c hrun (by simpa [hs] using hh)
      m (by simpa [hs] using hm)

theorem bound (B : Nat) (hB : 224707 ≤ B) :
    ∀ m, compatible table m → WeightedBound B m := by
  obtain ⟨hr,hh,hw⟩ := zipQueryOK_sound (lateQueryOK B hB)
  cases hrun : knownRun table 224705 with
  | none => simp [hrun] at hr
  | some c =>
    have hs : readSlot c = (0,true) := by simpa [hrun] using hr
    exact last_hole_sound B table 224705 c (by decide) hrun
      (by simpa [hs] using hh)
      (by simpa [hs] using restOK_sound table (0,true) (by decide))
      (by simpa [hs] using weightOK_sound table (0,true) 224705 B hw)

theorem exact_weighted (B : Nat) :
    (∀ m, compatible table m → WeightedBound B m) ↔ 224707 ≤ B := by
  constructor
  · intro h
    have hh : ∀ m, compatible (refine table (0,true) none) m → WeightedBound B m := by
      intro m hm
      exact h m (refine_preserves_compat table m (0,true) none (by decide) hm)
    have hd := (uniform_halter_weight_iff (refine table (0,true) none) B 224705
      (by decide) exact_halt).mp hh
    have h1 := hd 1 (by rw [delays_exact]; decide)
    omega
  · exact bound B

#print axioms lateChecked
#print axioms exact_halt
#print axioms bound
#print axioms exact_weighted
end BB6.Agent13Raw120Late1341
