import ChampionF1ZeroLFIntegration
import ChampionF1CycleSiblings

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent31F1CycleIntegration

open BB6Coverage BB6.Agent6ChampionResidual BB6.Agent47Canonical78 BB6.Agent10FastAudit
open BB6.Agent31F1CycleSiblings BB6.Agent48F1ZeroLFIntegration
open BB6.Agent31ChampionParentIntegration BB6.Agent31FourHoleRoster

/-- Lift any source-checked F1 cycle sibling from six steps to B. -/
theorem cover_cycle_parent (code : Nat) (tree : Audit)
    (hcheck : fastCheck 6 (parent code) tree = true)
    (B : Nat) (hB : 6 ≤ B) :
    Cover (WeightedBound B) (parent code) := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (all_completions_weighted code tree hcheck m hm k d hk hd) hB

def closedF1Cycles (p : PartialMachine) : Bool :=
  sameTable p (parent 1) ||
  sameTable p (parent 4) ||
  sameTable p (parent 7) ||
  sameTable p (parent 8) ||
  sameTable p (parent 10) ||
  sameTable p (parent 11) ||
  sameTable p (parent 16) ||
  sameTable p (parent 18)

/-- The 108-leaf raw139 frontier after 0LF, with eight exact cycle siblings
    removed and every other leaf retained. -/
noncomputable def remainingF1Cycles :
    List (List Move × PartialMachine) :=
  remainingF1ZeroLF.filter (fun e => !closedF1Cycles e.2)

theorem sameTable_false_of_not_true (p q : PartialMachine)
    (h : sameTable p q ≠ true) : sameTable p q = false := by
  cases hst : sameTable p q with
  | false => rfl
  | true => exact False.elim (h hst)

theorem parent0RA_present :
    ∃ e ∈ remainingF1ZeroLF, sameTable e.2 (parent 1) = true := by decide
theorem parent0LB_present :
    ∃ e ∈ remainingF1ZeroLF, sameTable e.2 (parent 4) = true := by decide
theorem parent1RB_present :
    ∃ e ∈ remainingF1ZeroLF, sameTable e.2 (parent 7) = true := by decide
theorem parent0LC_present :
    ∃ e ∈ remainingF1ZeroLF, sameTable e.2 (parent 8) = true := by decide
theorem parent1LC_present :
    ∃ e ∈ remainingF1ZeroLF, sameTable e.2 (parent 10) = true := by decide
theorem parent1RC_present :
    ∃ e ∈ remainingF1ZeroLF, sameTable e.2 (parent 11) = true := by decide
theorem parent0LE_present :
    ∃ e ∈ remainingF1ZeroLF, sameTable e.2 (parent 16) = true := by decide
theorem parent1LE_present :
    ∃ e ∈ remainingF1ZeroLF, sameTable e.2 (parent 18) = true := by decide

theorem remainingF1Cycles_count : remainingF1Cycles.length = 100 := by decide
theorem removedF1Cycle_count :
    remainingF1ZeroLF.length - remainingF1Cycles.length = 8 := by decide

/-- Each old leaf is either one of the eight checked cycle parents or remains
    in the 100-leaf residual list. -/
theorem cover_remainingF1ZeroLF
    (hLeaves : ∀ e ∈ remainingF1Cycles,
      Cover (WeightedBound championScore) e.2)
    (e : List Move × PartialMachine)
    (he : e ∈ remainingF1ZeroLF) :
    Cover (WeightedBound championScore) e.2 := by
  by_cases h0RA : sameTable e.2 (parent 1) = true
  · have heq : e.2 = parent 1 := sameTable_sound h0RA
    rw [heq]
    exact cover_cycle_parent 1 tree0RA checked0RA championScore
      (Nat.le_trans (by decide) champion_score_ge_49394)
  · by_cases h0LB : sameTable e.2 (parent 4) = true
    · have heq : e.2 = parent 4 := sameTable_sound h0LB
      rw [heq]
      exact cover_cycle_parent 4 tree0LB checked0LB championScore
        (Nat.le_trans (by decide) champion_score_ge_49394)
    · by_cases h1RB : sameTable e.2 (parent 7) = true
      · have heq : e.2 = parent 7 := sameTable_sound h1RB
        rw [heq]
        exact cover_cycle_parent 7 tree1RB checked1RB championScore
          (Nat.le_trans (by decide) champion_score_ge_49394)
      · by_cases h0LC : sameTable e.2 (parent 8) = true
        · have heq : e.2 = parent 8 := sameTable_sound h0LC
          rw [heq]
          exact cover_cycle_parent 8 tree0LC checked0LC championScore
            (Nat.le_trans (by decide) champion_score_ge_49394)
        · by_cases h1LC : sameTable e.2 (parent 10) = true
          · have heq : e.2 = parent 10 := sameTable_sound h1LC
            rw [heq]
            exact cover_cycle_parent 10 tree1LC checked1LC championScore
              (Nat.le_trans (by decide) champion_score_ge_49394)
          · by_cases h1RC : sameTable e.2 (parent 11) = true
            · have heq : e.2 = parent 11 := sameTable_sound h1RC
              rw [heq]
              exact cover_cycle_parent 11 tree1RC checked1RC championScore
                (Nat.le_trans (by decide) champion_score_ge_49394)
            · by_cases h0LE : sameTable e.2 (parent 16) = true
              · have heq : e.2 = parent 16 := sameTable_sound h0LE
                rw [heq]
                exact cover_cycle_parent 16 tree0LE checked0LE championScore
                  (Nat.le_trans (by decide) champion_score_ge_49394)
              · by_cases h1LE : sameTable e.2 (parent 18) = true
                · have heq : e.2 = parent 18 := sameTable_sound h1LE
                  rw [heq]
                  exact cover_cycle_parent 18 tree1LE checked1LE championScore
                    (Nat.le_trans (by decide) champion_score_ge_49394)
                · apply hLeaves e
                  apply List.mem_filter.mpr
                  refine ⟨he, ?_⟩
                  have h0RA' := sameTable_false_of_not_true _ _ h0RA
                  have h0LB' := sameTable_false_of_not_true _ _ h0LB
                  have h1RB' := sameTable_false_of_not_true _ _ h1RB
                  have h0LC' := sameTable_false_of_not_true _ _ h0LC
                  have h1LC' := sameTable_false_of_not_true _ _ h1LC
                  have h1RC' := sameTable_false_of_not_true _ _ h1RC
                  have h0LE' := sameTable_false_of_not_true _ _ h0LE
                  have h1LE' := sameTable_false_of_not_true _ _ h1LE
                  simp [closedF1Cycles, h0RA', h0LB', h1RB', h0LC',
                    h1LC', h1RC', h0LE', h1LE']

/-- Conditional exactness after eight new cycle siblings: 77 nonchampion
    canonical Covers and 100 explicit raw139 leaves remain. -/
theorem exact_from_remainingF1Cycles
    (hOther : ∀ e ∈ BB6.Agent47Canonical78.roster,
      e.2 ≠ championResidual →
        Cover (WeightedBound championScore) e.2)
    (hLeaves : ∀ e ∈ remainingF1Cycles,
      Cover (WeightedBound championScore) e.2) :
    BB6.Coverage.ExactBB6 championScore :=
  exact_from_remainingF1ZeroLF hOther
    (fun e he => cover_remainingF1ZeroLF hLeaves e he)

#print axioms cover_cycle_parent
#print axioms parent0RA_present
#print axioms parent0LB_present
#print axioms parent1RB_present
#print axioms parent0LC_present
#print axioms parent1LC_present
#print axioms parent1RC_present
#print axioms parent0LE_present
#print axioms parent1LE_present
#print axioms remainingF1Cycles_count
#print axioms cover_remainingF1ZeroLF
#print axioms exact_from_remainingF1Cycles

end BB6.Agent31F1CycleIntegration
