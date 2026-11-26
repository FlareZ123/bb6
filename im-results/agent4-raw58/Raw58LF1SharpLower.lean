import Raw58LF1Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent4Raw58LF1
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6Coverage.Agent4LF1Sweep
abbrev q1 := refine parent (2,true) (some ⟨true,true,2⟩)
abbrev q2 := refine q1 (4,false) (some ⟨true,false,2⟩)
abbrev q3 := refine q2 (5,false) (some ⟨false,false,0⟩)
abbrev q4 := refine q3 (5,true) (some ⟨false,false,5⟩)

theorem q4_table : q4 = table .v86 := tableOK_sound _ _ (by decide)

theorem delays_exact : possibleDelays (refine (table .v86) (1,true) none) 0 = [0,1] := by decide

theorem exact_halt (m : Machine) (hm : compatible (refine (table .v86) (1,true) none) m) :
    HaltsAfter m 3055744 := by
  have hq : zipQueryOK 3055750 (table .v86) 3055744 (1,true) = true := by
    have h := lastCheck .v86 3055750 (by decide)
    change (zipQueryOK 3055750 (table .v86) 3055744 (1,true) && restOK (table .v86) (1,true)) = true at h
    simp only [Bool.and_eq_true] at h
    exact h.1
  obtain ⟨hr,hh,_⟩ := zipQueryOK_sound hq
  cases hrun : knownRun (table .v86) 3055744 with
  | none => simp [hrun] at hr
  | some c =>
    have hs : readSlot c = (1,true) := by simpa [hrun] using hr
    exact first_hole_halts (table .v86) 3055744 c hrun (by simpa [hs] using hh) m (by simpa [hs] using hm)

theorem leaf_compat (m : Machine) (hm : compatible (refine (table .v86) (1,true) none) m) : compatible parent m := by
  have h4 : compatible q4 m := by
    rw [q4_table]
    exact refine_preserves_compat _ _ _ _ (by decide) hm
  have h3 : compatible q3 m := refine_preserves_compat _ _ _ _ (by decide) h4
  have h2 : compatible q2 m := refine_preserves_compat _ _ _ _ (by decide) h3
  have h1 : compatible q1 m := refine_preserves_compat _ _ _ _ (by decide) h2
  exact refine_preserves_compat _ _ _ _ (by decide) h1

theorem lower (B : Nat) (h : ∀ m, compatible parent m → WeightedBound B m) : 3055746 ≤ B := by
  have hh : ∀ m, compatible (refine (table .v86) (1,true) none) m → WeightedBound B m :=
    fun m hm => h m (leaf_compat m hm)
  have hd := (uniform_halter_weight_iff _ B 3055744 (by decide) exact_halt).mp hh
  have h1 := hd 1 (by rw [delays_exact]; decide)
  omega

#print axioms lower
end BB6.Agent4Raw58LF1
