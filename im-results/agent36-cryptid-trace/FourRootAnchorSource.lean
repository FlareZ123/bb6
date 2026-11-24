import DAllBlankHalting
import RegularBands
import DRegularSourceShift
import Lean.Elab.Tactic.Omega

namespace BB6.Agent36

open CryptidBoundary
open BB6.Agent26.GrowthBands
open BB6.BoundaryPadding

/-- The four DRegular arithmetic seeds are exactly the original-source
unary sections reached by the authenticated blank-root prefixes. -/
private theorem seed5_section :
    DRegularSource.sourceSection (seed 0) =
      CryptidBoundary.init (List.replicate 3 true) := by
  simp [DRegularSource.sourceSection, seed, CryptidBoundary.oppairs]

private theorem seed9_section :
    DRegularSource.sourceSection (seed 1) =
      CryptidBoundary.init (List.replicate 7 true) := by
  simp [DRegularSource.sourceSection, seed, CryptidBoundary.oppairs]

private theorem seed15_section :
    DRegularSource.sourceSection (seed 2) =
      CryptidBoundary.init (List.replicate 13 true) := by
  simp [DRegularSource.sourceSection, seed, CryptidBoundary.oppairs]

private theorem seed39_section :
    DRegularSource.sourceSection (seed 3) =
      CryptidBoundary.init (List.replicate 37 true) := by
  simp [DRegularSource.sourceSection, seed, CryptidBoundary.oppairs]

theorem root_D3_to_seed5 :
    CryptidBoundary.run 15 (sourceBlank (3 : Fin 6)) =
      DRegularSource.sourceSection (seed 0) := by
  rw [seed5_section]
  exact source_blank_D15

theorem root_D0_to_seed9 :
    CryptidBoundary.run 36 (sourceBlank (0 : Fin 6)) =
      DRegularSource.sourceSection (seed 1) := by
  rw [seed9_section]
  exact source_blank_A36

theorem root_D2_to_seed15 :
    CryptidBoundary.run 92 (sourceBlank (2 : Fin 6)) =
      DRegularSource.sourceSection (seed 2) := by
  rw [seed15_section]
  exact source_blank_C92

theorem root_D1_to_seed39 :
    CryptidBoundary.run 403 (sourceBlank (5 : Fin 6)) =
      DRegularSource.sourceSection (seed 3) := by
  rw [seed39_section]
  exact source_blank_F403

private theorem seed0_canon : DRegular.Canon (seed 0) := by
  constructor
  · simp [seed]
  · exact Or.inr rfl

private theorem seed1_canon : DRegular.Canon (seed 1) := by
  constructor
  · simp [seed]
  · exact Or.inr rfl

private theorem seed2_canon : DRegular.Canon (seed 2) := by
  constructor
  · simp [seed]
  · exact Or.inr rfl

private theorem seed3_canon : DRegular.Canon (seed 3) := by
  constructor
  · simp [seed]
  · exact Or.inr rfl

/-- The source-authenticated eleven-row contract transports every
canonical DRegular path to an original-machine observational return. -/
private theorem seed0_to_anchor0 :
    ObsEq
      (CryptidBoundary.run (DRegular.accumulated (shift 0) (seed 0))
        (DRegularSource.sourceSection (seed 0)))
      (DRegularSource.sourceSection (anchor 0)) := by
  have hc : DRegular.Canon (seed 0) := seed0_canon
  exact (BB6.DRegularSourceShift.paired_original_run
    (seed 0) (anchor 0) (shift 0) 0 hc (anchor_run 0)).1

private theorem seed1_to_anchor1 :
    ObsEq
      (CryptidBoundary.run (DRegular.accumulated (shift 1) (seed 1))
        (DRegularSource.sourceSection (seed 1)))
      (DRegularSource.sourceSection (anchor 1)) := by
  have hc : DRegular.Canon (seed 1) := seed1_canon
  exact (BB6.DRegularSourceShift.paired_original_run
    (seed 1) (anchor 1) (shift 1) 0 hc (anchor_run 1)).1

private theorem seed2_to_anchor2 :
    ObsEq
      (CryptidBoundary.run (DRegular.accumulated (shift 2) (seed 2))
        (DRegularSource.sourceSection (seed 2)))
      (DRegularSource.sourceSection (anchor 2)) := by
  have hc : DRegular.Canon (seed 2) := seed2_canon
  exact (BB6.DRegularSourceShift.paired_original_run
    (seed 2) (anchor 2) (shift 2) 0 hc (anchor_run 2)).1

private theorem seed3_to_anchor3 :
    ObsEq
      (CryptidBoundary.run (DRegular.accumulated (shift 3) (seed 3))
        (DRegularSource.sourceSection (seed 3)))
      (DRegularSource.sourceSection (anchor 3)) := by
  have hc : DRegular.Canon (seed 3) := seed3_canon
  exact (BB6.DRegularSourceShift.paired_original_run
    (seed 3) (anchor 3) (shift 3) 0 hc (anchor_run 3)).1

/-- D3's authentic blank root reaches the first widened phase-band anchor. -/
theorem root_D3_to_anchor :
    ObsEq
      (CryptidBoundary.run
        (15 + DRegular.accumulated (shift 0) (seed 0))
        (sourceBlank (3 : Fin 6)))
      (DRegularSource.sourceSection (anchor 0)) := by
  rw [CryptidBoundary.run_add, root_D3_to_seed5]
  exact seed0_to_anchor0

/-- D0's authentic blank root reaches the second widened phase-band anchor. -/
theorem root_D0_to_anchor :
    ObsEq
      (CryptidBoundary.run
        (36 + DRegular.accumulated (shift 1) (seed 1))
        (sourceBlank (0 : Fin 6)))
      (DRegularSource.sourceSection (anchor 1)) := by
  rw [CryptidBoundary.run_add, root_D0_to_seed9]
  exact seed1_to_anchor1

/-- D2's authentic blank root reaches the third widened phase-band anchor. -/
theorem root_D2_to_anchor :
    ObsEq
      (CryptidBoundary.run
        (92 + DRegular.accumulated (shift 2) (seed 2))
        (sourceBlank (2 : Fin 6)))
      (DRegularSource.sourceSection (anchor 2)) := by
  rw [CryptidBoundary.run_add, root_D2_to_seed15]
  exact seed2_to_anchor2

/-- D1's authentic blank root reaches the fourth widened phase-band anchor. -/
theorem root_D1_to_anchor :
    ObsEq
      (CryptidBoundary.run
        (403 + DRegular.accumulated (shift 3) (seed 3))
        (sourceBlank (5 : Fin 6)))
      (DRegularSource.sourceSection (anchor 3)) := by
  rw [CryptidBoundary.run_add, root_D1_to_seed39]
  exact seed3_to_anchor3

/-- Observational equality preserves the complete frozen-state
halting predicate at every future time. -/
theorem source_halts_iff_obsEq {c d : CryptidBoundary.Cfg}
    (h : ObsEq c d) : SourceHalts c ↔ SourceHalts d := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hs := (source_congr n h).2.2.2
    change (CryptidBoundary.run n c).st =
      (CryptidBoundary.run n d).st at hs
    exact ⟨n, hs ▸ hn⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hs := (source_congr n h).2.2.2
    change (CryptidBoundary.run n c).st =
      (CryptidBoundary.run n d).st at hs
    exact hs.symm ▸ hn

/-- Each of the four authentic source-table blank starts has exactly the
same all-time halting status as its large DRegular anchor section. -/
theorem source_D3_halts_iff_anchor :
    SourceHalts (sourceBlank (3 : Fin 6)) ↔
      SourceHalts (DRegularSource.sourceSection (anchor 0)) :=
  (halts_after_exact_prefix 15 _ _ root_D3_to_seed5).trans
    (source_halts_iff_obsEq seed0_to_anchor0)

theorem source_D0_halts_iff_anchor :
    SourceHalts (sourceBlank (0 : Fin 6)) ↔
      SourceHalts (DRegularSource.sourceSection (anchor 1)) :=
  (halts_after_exact_prefix 36 _ _ root_D0_to_seed9).trans
    (source_halts_iff_obsEq seed1_to_anchor1)

theorem source_D2_halts_iff_anchor :
    SourceHalts (sourceBlank (2 : Fin 6)) ↔
      SourceHalts (DRegularSource.sourceSection (anchor 2)) :=
  (halts_after_exact_prefix 92 _ _ root_D2_to_seed15).trans
    (source_halts_iff_obsEq seed2_to_anchor2)

theorem source_D1_halts_iff_anchor :
    SourceHalts (sourceBlank (5 : Fin 6)) ↔
      SourceHalts (DRegularSource.sourceSection (anchor 3)) :=
  (halts_after_exact_prefix 403 _ _ root_D1_to_seed39).trans
    (source_halts_iff_obsEq seed3_to_anchor3)

/-- The four original-source endpoints have exactly the arithmetic measures
used by the widened phase-band separation theorem. -/
theorem anchor_measures :
    measure (anchor 0) = base 0 ∧
    measure (anchor 1) = base 1 ∧
    measure (anchor 2) = base 2 ∧
    measure (anchor 3) = base 3 := by
  exact ⟨anchor_measure 0, anchor_measure 1, anchor_measure 2, anchor_measure 3⟩

#print axioms root_D3_to_seed5
#print axioms root_D0_to_seed9
#print axioms root_D2_to_seed15
#print axioms root_D1_to_seed39
#print axioms root_D3_to_anchor
#print axioms root_D0_to_anchor
#print axioms root_D2_to_anchor
#print axioms root_D1_to_anchor
#print axioms anchor_measures
#print axioms source_halts_iff_obsEq
#print axioms source_D3_halts_iff_anchor
#print axioms source_D0_halts_iff_anchor
#print axioms source_D2_halts_iff_anchor
#print axioms source_D1_halts_iff_anchor

end BB6.Agent36
