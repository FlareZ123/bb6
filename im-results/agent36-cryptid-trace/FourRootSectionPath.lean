import FourRootAnchorSource
import SourceSectionBandsAdapter
import SectionBands
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 65536
set_option maxHeartbeats 100000000

namespace BB6.Agent36.FourRootSectionPath

open CryptidBoundary
open BB6.OneSided
open BB6.Agent26.GrowthBands
open BB6.Agent36
open BB6.Agent36.SourceSectionBandsAdapter
open BB6.Agent36.SectionBandSeparation

/-- The source macro's Section(n,v) is exactly the initial configuration
obtained by adding the two fixed leading ones to a unary prefix of length n-2. -/
private theorem init_section_eq (n : Nat) (hn : 2 ≤ n) (v : List Bool) :
    CryptidBoundary.init (List.replicate (n - 2) true ++ v) =
      BB6.OneSided.Section n v := by
  simp only [BB6.OneSided.Section, CryptidBoundary.init]
  congr 1
  change true :: true :: (List.replicate (n - 2) true ++ v) =
    List.replicate n true ++ v
  calc
    true :: true :: (List.replicate (n - 2) true ++ v) =
        List.replicate 2 true ++ List.replicate (n - 2) true ++ v := by rfl
    _ = List.replicate (2 + (n - 2)) true ++ v := by
          rw [List.replicate_append_replicate]
    _ = List.replicate n true ++ v := by
          congr 1
          simpa [Nat.add_comm] using Nat.sub_add_cancel hn

/-- The original DRegular source encoding is the exact one-sided section
used by Agent 32, with suffix (01)^q 1^b. -/
private theorem sourceSection_eq_section (s : DRegular.L) (hs : 2 ≤ s.a) :
    DRegularSource.sourceSection s =
      BB6.OneSided.Section s.a
        (CryptidBoundary.oppairs s.q ++ List.replicate s.b true) := by
  unfold DRegularSource.sourceSection
  rw [List.append_assoc, init_section_eq s.a hs]

def anchorSuffix0 : List Bool :=
  CryptidBoundary.oppairs (anchor 0).q ++ List.replicate (anchor 0).b true

def anchorSuffix1 : List Bool :=
  CryptidBoundary.oppairs (anchor 1).q ++ List.replicate (anchor 1).b true

def anchorSuffix2 : List Bool :=
  CryptidBoundary.oppairs (anchor 2).q ++ List.replicate (anchor 2).b true

def anchorSuffix3 : List Bool :=
  CryptidBoundary.oppairs (anchor 3).q ++ List.replicate (anchor 3).b true

theorem anchor0_section_eq :
    DRegularSource.sourceSection (anchor 0) =
      BB6.OneSided.Section (anchor 0).a anchorSuffix0 := by
  simpa [anchorSuffix0] using
    sourceSection_eq_section (anchor 0) (by decide)

theorem anchor1_section_eq :
    DRegularSource.sourceSection (anchor 1) =
      BB6.OneSided.Section (anchor 1).a anchorSuffix1 := by
  simpa [anchorSuffix1] using
    sourceSection_eq_section (anchor 1) (by decide)

theorem anchor2_section_eq :
    DRegularSource.sourceSection (anchor 2) =
      BB6.OneSided.Section (anchor 2).a anchorSuffix2 := by
  simpa [anchorSuffix2] using
    sourceSection_eq_section (anchor 2) (by decide)

theorem anchor3_section_eq :
    DRegularSource.sourceSection (anchor 3) =
      BB6.OneSided.Section (anchor 3).a anchorSuffix3 := by
  simpa [anchorSuffix3] using
    sourceSection_eq_section (anchor 3) (by decide)

theorem anchor0_head : BB6.OneSided.head anchorSuffix0 = false := by decide
theorem anchor1_head : BB6.OneSided.head anchorSuffix1 = false := by decide
theorem anchor2_head : BB6.OneSided.head anchorSuffix2 = false := by decide
theorem anchor3_head : BB6.OneSided.head anchorSuffix3 = false := by decide

theorem anchor0_measure :
    sourceMeasure (anchor 0).a anchorSuffix0 = base 0 := by decide

theorem anchor1_measure :
    sourceMeasure (anchor 1).a anchorSuffix1 = base 1 := by decide

theorem anchor2_measure :
    sourceMeasure (anchor 2).a anchorSuffix2 = base 2 := by decide

theorem anchor3_measure :
    sourceMeasure (anchor 3).a anchorSuffix3 = base 3 := by decide

/-- Under a nonhalting hypothesis, the arbitrary-suffix theorem can be
iterated indefinitely. Every chosen return is an exact source equality,
retains a normalized suffix, and contributes one Edge135 step. No
first-return minimality is assumed or needed. -/
theorem exists_path_of_nonhalting {n : Nat} {v : List Bool}
    (hn : 5 ≤ n) (hv : BB6.OneSided.head v = false)
    (hnh : ¬ SourceHalts (BB6.OneSided.Section n v)) :
    ∀ k, ∃ n' v', Path135 k (sourceMeasure n v) (sourceMeasure n' v') ∧
      ¬ SourceHalts (BB6.OneSided.Section n' v') := by
  suffices h : ∀ k n v, 5 ≤ n → BB6.OneSided.head v = false →
      ¬ SourceHalts (BB6.OneSided.Section n v) →
      ∃ n' v', Path135 k (sourceMeasure n v) (sourceMeasure n' v') ∧
        ¬ SourceHalts (BB6.OneSided.Section n' v') by
    intro k
    exact h k n v hn hv hnh
  intro k
  induction k with
  | zero =>
      intro n v hn hv hnh
      exact ⟨n, v, Path135.nil (sourceMeasure n v), hnh⟩
  | succ k ih =>
      intro n v hn hv hnh
      rcases section_edge_or_halt hn hv with hhalt | ⟨t, n', v', ht, hrun, hv', hedge⟩
      · apply False.elim
        apply hnh
        rcases hhalt with ⟨u, hu, hstate⟩
        exact ⟨u, hstate⟩
      · have hnh' : ¬ SourceHalts (BB6.OneSided.Section n' v') := by
          intro hh
          have hiff := halts_after_exact_prefix t
            (BB6.OneSided.Section n v) (BB6.OneSided.Section n' v') hrun
          exact hnh (hiff.mpr hh)
        have hn' : 5 ≤ n' := edge_live hedge
        obtain ⟨n'', v'', hp, hnh''⟩ := ih n' v' hn' hv' hnh'
        exact ⟨n'', v'', Path135.cons hedge hp, hnh''⟩

/-- Each authentic D3 source start, if nonhalting, generates an infinite
family of exact source sections whose measures follow Path135 from base 0. -/
theorem source_D3_path_of_nonhalting
    (hroot : ¬ SourceHalts (sourceBlank (3 : Fin 6))) :
    ∀ k, ∃ n' v', Path135 k (base 0) (sourceMeasure n' v') ∧
      ¬ SourceHalts (BB6.OneSided.Section n' v') := by
  have hiff : SourceHalts (sourceBlank (3 : Fin 6)) ↔
      SourceHalts (BB6.OneSided.Section (anchor 0).a anchorSuffix0) := by
    simpa only [anchor0_section_eq] using source_D3_halts_iff_anchor
  have hanchor : ¬ SourceHalts (BB6.OneSided.Section (anchor 0).a anchorSuffix0) := by
    intro hh
    exact hroot (hiff.mpr hh)
  intro k
  obtain ⟨n', v', hp, hnh'⟩ :=
    exists_path_of_nonhalting (n := (anchor 0).a) (v := anchorSuffix0)
      (by decide) anchor0_head hanchor k
  exact ⟨n', v', by simpa [anchor0_measure] using hp, hnh'⟩

theorem source_D0_path_of_nonhalting
    (hroot : ¬ SourceHalts (sourceBlank (0 : Fin 6))) :
    ∀ k, ∃ n' v', Path135 k (base 1) (sourceMeasure n' v') ∧
      ¬ SourceHalts (BB6.OneSided.Section n' v') := by
  have hiff : SourceHalts (sourceBlank (0 : Fin 6)) ↔
      SourceHalts (BB6.OneSided.Section (anchor 1).a anchorSuffix1) := by
    simpa only [anchor1_section_eq] using source_D0_halts_iff_anchor
  have hanchor : ¬ SourceHalts (BB6.OneSided.Section (anchor 1).a anchorSuffix1) := by
    intro hh
    exact hroot (hiff.mpr hh)
  intro k
  obtain ⟨n', v', hp, hnh'⟩ :=
    exists_path_of_nonhalting (n := (anchor 1).a) (v := anchorSuffix1)
      (by decide) anchor1_head hanchor k
  exact ⟨n', v', by simpa [anchor1_measure] using hp, hnh'⟩

theorem source_D2_path_of_nonhalting
    (hroot : ¬ SourceHalts (sourceBlank (2 : Fin 6))) :
    ∀ k, ∃ n' v', Path135 k (base 2) (sourceMeasure n' v') ∧
      ¬ SourceHalts (BB6.OneSided.Section n' v') := by
  have hiff : SourceHalts (sourceBlank (2 : Fin 6)) ↔
      SourceHalts (BB6.OneSided.Section (anchor 2).a anchorSuffix2) := by
    simpa only [anchor2_section_eq] using source_D2_halts_iff_anchor
  have hanchor : ¬ SourceHalts (BB6.OneSided.Section (anchor 2).a anchorSuffix2) := by
    intro hh
    exact hroot (hiff.mpr hh)
  intro k
  obtain ⟨n', v', hp, hnh'⟩ :=
    exists_path_of_nonhalting (n := (anchor 2).a) (v := anchorSuffix2)
      (by decide) anchor2_head hanchor k
  exact ⟨n', v', by simpa [anchor2_measure] using hp, hnh'⟩

theorem source_D1_path_of_nonhalting
    (hroot : ¬ SourceHalts (sourceBlank (5 : Fin 6))) :
    ∀ k, ∃ n' v', Path135 k (base 3) (sourceMeasure n' v') ∧
      ¬ SourceHalts (BB6.OneSided.Section n' v') := by
  have hiff : SourceHalts (sourceBlank (5 : Fin 6)) ↔
      SourceHalts (BB6.OneSided.Section (anchor 3).a anchorSuffix3) := by
    simpa only [anchor3_section_eq] using source_D1_halts_iff_anchor
  have hanchor : ¬ SourceHalts (BB6.OneSided.Section (anchor 3).a anchorSuffix3) := by
    intro hh
    exact hroot (hiff.mpr hh)
  intro k
  obtain ⟨n', v', hp, hnh'⟩ :=
    exists_path_of_nonhalting (n := (anchor 3).a) (v := anchorSuffix3)
      (by decide) anchor3_head hanchor k
  exact ⟨n', v', by simpa [anchor3_measure] using hp, hnh'⟩

/-- Any two nonhalting-root return paths are disjoint in unary section
length unless they have both the same root ordinal and the same return count. -/
theorem source_paths_disjoint {a b : Fin 4} {i j : Nat}
    {x y : BB6.Agent26.GrowthBands.Section} (p : Path135 i (base a) x) (q : Path135 j (base b) y)
    (h : a ≠ b ∨ i ≠ j) : x.n ≠ y.n :=
  disjoint_paths p q h

#print axioms exists_path_of_nonhalting
#print axioms source_D3_path_of_nonhalting
#print axioms source_D0_path_of_nonhalting
#print axioms source_D2_path_of_nonhalting
#print axioms source_D1_path_of_nonhalting
#print axioms source_paths_disjoint

end BB6.Agent36.FourRootSectionPath
