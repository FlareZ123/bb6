import Raw122ExceptionalLeaves
import Raw122Roster16Witnesses
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122Roster
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6.Agent43Raw122 BB6.Agent43Raw122ResidualCompose BB6.Agent43Raw122Sharp BB6.Agent43Raw122Exceptional

/-- The actual residual list of each ordinary F0 child lies in the
published roster. This preserves machine-specific exceptions rather
than replacing them by a uniform upper bound. -/
theorem kids16_residual_mem (mv : Move) :
    ∀ e ∈ partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some mv)) (kids16 mv),
      e.2 ∈ tables16 := by
  intro e he
  have hmem : e.2 ∈ (partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some mv)) (kids16 mv)).map Prod.snd :=
    List.mem_map.mpr ⟨e,he,rfl⟩
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  · change e.2 ∈ (partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,false,0⟩)) kid16_00).map Prod.snd at hmem
    rw [kid16_00_roster] at hmem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
    rw [hmem]
    simp [tables16]
  · change e.2 ∈ (partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,true,0⟩)) kid16_06).map Prod.snd at hmem
    rw [kid16_06_roster] at hmem
    simp at hmem
  · change e.2 ∈ (partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨true,false,0⟩)) kid16_12).map Prod.snd at hmem
    rw [kid16_12_roster] at hmem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
    rcases hmem with h|h <;> rw [h] <;> simp [tables16]
  · change e.2 ∈ (partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨true,true,0⟩)) kid16_18).map Prod.snd at hmem
    rw [kid16_18_roster] at hmem
    simp at hmem
  · change e.2 ∈ (partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,false,1⟩)) kid16_01).map Prod.snd at hmem
    rw [kid16_01_roster] at hmem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
    rcases hmem with h|h|h|h <;> rw [h] <;> simp [tables16]
  · change e.2 ∈ (partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,true,1⟩)) kid16_07).map Prod.snd at hmem
    rw [kid16_07_roster] at hmem
    simp at hmem
  · change e.2 ∈ (partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨true,false,1⟩)) kid16_13).map Prod.snd at hmem
    rw [kid16_13_roster] at hmem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
    rcases hmem with h|h|h <;> rw [h] <;> simp [tables16]
  · change e.2 ∈ (partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨true,true,1⟩)) kid16_19).map Prod.snd at hmem
    rw [kid16_19_roster] at hmem
    simp at hmem
  · change e.2 ∈ (partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,false,2⟩)) kid16_02).map Prod.snd at hmem
    rw [kid16_02_roster] at hmem
    simp at hmem
  · change e.2 ∈ (partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,true,2⟩)) kid16_08).map Prod.snd at hmem
    rw [kid16_08_roster] at hmem
    simp at hmem
  · change e.2 ∈ (partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨true,false,2⟩)) kid16_14).map Prod.snd at hmem
    rw [kid16_14_roster] at hmem
    simp at hmem
  · change e.2 ∈ (partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨true,true,2⟩)) kid16_20).map Prod.snd at hmem
    rw [kid16_20_roster] at hmem
    simp at hmem
  · change e.2 ∈ (partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,false,3⟩)) kid16_03).map Prod.snd at hmem
    rw [kid16_03_roster] at hmem
    simp at hmem
  · change e.2 ∈ (partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,true,3⟩)) kid16_09).map Prod.snd at hmem
    rw [kid16_09_roster] at hmem
    simp at hmem
  · change e.2 ∈ (partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨true,false,3⟩)) kid16_15).map Prod.snd at hmem
    rw [kid16_15_roster] at hmem
    simp at hmem
  · change e.2 ∈ (partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨true,true,3⟩)) kid16_21).map Prod.snd at hmem
    rw [kid16_21_roster] at hmem
    simp at hmem
  · change e.2 ∈ (partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,false,4⟩)) kid16_04).map Prod.snd at hmem
    rw [kid16_04_roster] at hmem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
    rcases hmem with h|h|h <;> rw [h] <;> simp [tables16]
  · change e.2 ∈ (partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,true,4⟩)) kid16_10).map Prod.snd at hmem
    rw [kid16_10_roster] at hmem
    simp at hmem
  · change e.2 ∈ (partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨true,false,4⟩)) kid16_16).map Prod.snd at hmem
    rw [kid16_16_roster] at hmem
    simp at hmem
  · change e.2 ∈ (partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨true,true,4⟩)) kid16_22).map Prod.snd at hmem
    rw [kid16_22_roster] at hmem
    simp at hmem
  · change e.2 ∈ (partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,false,5⟩)) kid16_05).map Prod.snd at hmem
    rw [kid16_05_roster] at hmem
    simp at hmem
  · change e.2 ∈ (partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,true,5⟩)) kid16_11).map Prod.snd at hmem
    rw [kid16_11_roster] at hmem
    simp at hmem
  · change e.2 ∈ (partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨true,false,5⟩)) kid16_17).map Prod.snd at hmem
    rw [kid16_17_roster] at hmem
    simp at hmem
  · change e.2 ∈ (partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨true,true,5⟩)) kid16_23).map Prod.snd at hmem
    rw [kid16_23_roster] at hmem
    simp at hmem

theorem branch16_residual_mem :
    ∀ e ∈ partialResiduals (BB6.Agent43Raw122.child ⟨true,false,4⟩) branch16, e.2 ∈ tables16 := by
  intro e he
  change e ∈ partialResiduals (BB6.Agent43Raw122.child ⟨true,false,4⟩) (.split 9 (5,false) kids16) at he
  rw [partialResiduals.eq_3] at he
  obtain ⟨mv,_,hh⟩ := List.mem_flatMap.mp he
  obtain ⟨e',he',heq⟩ := List.mem_map.mp hh
  rw [← heq]
  exact kids16_residual_mem mv e' he'

theorem witnesses16_except (p : PartialMachine) (hp : p ∈ tables16)
    (m : Machine) (hm : compatible p m) (hne : m ≠ second) : WeightedBound 7014 m := by
  simp only [tables16,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · have he : p16_000 = BB6Coverage.Agent29Raw122Indexed.M067.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he] at hm
    exact (never_bound (C := 7014) (BB6Coverage.Agent29Raw122Indexed.M067.never)) m hm
  · have he : p16_001 = BB6Coverage.Agent29Raw122Indexed.M068.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he] at hm
    exact (never_bound (C := 7014) (BB6Coverage.Agent29Raw122Indexed.M068.never)) m hm
  · have he : p16_002 = BB6Coverage.Agent29Raw122Indexed.M071.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he] at hm
    exact (never_bound (C := 7014) (BB6Coverage.Agent29Raw122Indexed.M071.never)) m hm
  · have he : p16_003 = BB6Coverage.Agent29Raw122Indexed.M069.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he] at hm
    exact (never_bound (C := 7014) (BB6Coverage.Agent29Raw122Indexed.M069.never)) m hm
  · have he : p16_004 = BB6Coverage.Agent29Raw122Indexed.M070.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he] at hm
    exact (never_bound (C := 7014) (BB6Coverage.Agent29Raw122Indexed.M070.never)) m hm
  · have he : p16_005 = BB6Coverage.Agent29Raw122Indexed.M073.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he] at hm
    exact (never_bound (C := 7014) (BB6Coverage.Agent29Raw122Indexed.M073.never)) m hm
  · have he : p16_006 = BB6Coverage.Agent29Raw122Indexed.M074.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he] at hm
    exact (never_bound (C := 7014) (BB6Coverage.Agent29Raw122Indexed.M074.never)) m hm
  · have he : p16_007 = BB6Coverage.Agent29Raw122Indexed.M072.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he] at hm
    exact (never_bound (C := 7014) (BB6Coverage.Agent29Raw122Indexed.M072.never)) m hm
  · have he : p16_008 = BB6Coverage.Agent29Raw122Indexed.M076.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he] at hm
    exact (never_bound (C := 7014) (BB6Coverage.Agent29Raw122Indexed.M076.never)) m hm
  · have he : p16_009 = BB6Coverage.Agent29Raw122Indexed.M075.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he] at hm
    exact (never_bound (C := 7014) (BB6Coverage.Agent29Raw122Indexed.M075.never)) m hm
  · have he : p16_010 = BB6Coverage.Agent31Pump.Raw122DirectGrowth.M90.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he] at hm
    exact (never_bound (C := 7014) (BB6Coverage.Agent31Pump.Raw122DirectGrowth.M90.never)) m hm
  · have he : p16_011 = BB6Coverage.Agent29Raw122Indexed.M077.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he] at hm
    exact (never_bound (C := 7014) (BB6Coverage.Agent29Raw122Indexed.M077.never)) m hm
  · have he : p16_012 = BB6Coverage.Agent29PackedLate.M1.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    have hm' : compatible BB6Coverage.Agent29PackedLate.M1.table m := by
      rw [← he]
      exact hm
    exact late1_other_bound m hm' hne

theorem cover16_except (m : Machine) (hm : compatible (BB6.Agent43Raw122.child ⟨true,false,4⟩) m)
    (hne : m ≠ second) : WeightedBound 7014 m := by
  rcases partialSound 7014 (BB6.Agent43Raw122.child ⟨true,false,4⟩) branch16 (by decide)
      (weightedTNFNoAssignedHalt_refine BB6.Agent43Raw122.parent (5,true) _ BB6.Agent43Raw122.parent_nohalt)
      branch16_checked m hm with h|⟨e,he,hh⟩
  · exact h
  · exact witnesses16_except e.2 (branch16_residual_mem e he) m hh hne
#print axioms cover16_except

end BB6.Agent43Raw122Roster
