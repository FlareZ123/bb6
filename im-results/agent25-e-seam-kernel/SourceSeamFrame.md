# Original-source E-sector context frame and strict first-event dichotomy

**Agent 25, 9 November 2026.** This is a Lean-checked theorem about the actual original six-state D machine's prepared E configurations. It is conditional on one precisely identified first-marker safety lemma, so it does **not** decide D's authentic blank run, BB(6), or a universal nonhalting property.

## The source theorem

Let `Boundary.lean` define the exact D table `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---` as `CryptidBoundary.Cfg`. Let `E_(3+k)(Y)` denote state E scanning zero with nearest-first left list `00(10)^(3+k)11`, and arbitrary finite right suffix `Y` (implicitly blank thereafter). Let `Core(Y)` have the left list `00(10)^3 1`, which stops immediately before the first protected marker; its last terminal 1 is still to its left. If `Core(Y)` first exhausts its left list at primitive time `t` in state C scanning 1, then for **every natural k**:

- `E_(3+k)(Y)` first reaches physically blank-left F/0 at **exactly t + 2k + 2 primitive steps**, with complete right list `1^(2k+2) ++ Core(t).right`;
- at every earlier time it reaches neither a physically blank-left F/0 return nor F/1 halt;
- the input shift `k → k+1` therefore contributes precisely 2 steps and 2 additional output ones, with all other output tape symbols preserved.

If `Core(Y)` never exhausts its left list, then every `E_(3+k)(Y)` avoids physically blank-left F/0 at **all times**, and the F/1 halt-gate predicate is exactly that of `Core(Y)` at the **same** time for every k. If the core does halt before hitting the marker, the frozen machine leaves the left list nonempty.

The source-level `eSector_source_dichotomy` combines both branches using one explicit hypothesis:

```lean
def SourceMarkerSafe (ys : List Bool) : Prop :=
  ∀ t : Nat,
    (∀ i : Nat, i < t → (run i (eCore ys)).l ≠ []) →
    (run t (eCore ys)).l = [] →
    (run t (eCore ys)).st = 2 ∧ (run t (eCore ys)).h = true
```

This is the exact remaining missing lemma to be transported from the separately certified E3 full physical marker invariant. The source theorem itself does **not** assume that the genuine blank orbit reaches a prepared E-sector state.

## Why the proof advances the source interface

`SourceSeamFrame.lean` proves a generic left-frame lemma directly from the **original** transition table: any untouched left suffix is invisible while the current source left list stays nonempty, for **arbitrary** right tape and **any** number of source steps. The source-exact identity `eSector_eq_append` identifies each whole E-sector with `Core` plus its untouched marker suffix. A retained terminal 1 makes a premature physically blank-left F/0 impossible. The existing [original-source marker sweep](../agent31-d-exceptional/ESeamSource.lean) processes the retained marker using exactly `2k+2` primitive steps and produces `2k+2` consecutive output ones. The additional `marker_sweep_no_F_before` and `core_no_early_halt` establish the strict first-event property. These statements are quantified across all stack lengths and all primitive times, and no finitary sample limit enters their proofs.

The right-tape universe here is the original source's arbitrary finite `List Bool` plus zero continuation. The earlier [complete-right-tape physical theorem](PhysicalWindowBridge.md) instead covers `Nat→Bool` arbitrary infinite tails; a frame-preserving representation map is still needed to compose them. This theorem does not yet establish the paper E-sector all-m result unconditionally inside the original source.

## Reproduction

The source is [SourceSeamFrame.lean.xz.b64](SourceSeamFrame.lean.xz.b64), restored by [restore_source_frame.py](restore_source_frame.py) with locked atomic write and SHA-256 `e65b53d0e989cc1c987ac733e07b9bdc6d0c450b74045dcb32d87aff682eb786`. Compile exact `Boundary.lean` from [Agent31's pinned original](../agent31-cryptid-boundary/unpack.py), then [ESeamSource.lean](../agent31-d-exceptional/ESeamSource.lean), then the restored source. Locally this compiled with Lean 4.36.0-rc2, no `sorry`, and only standard axioms `[propext, Classical.choice, Quot.sound]` for the full dichotomy. A selective [source-only CI workflow](../../.github/workflows/agent25-source-seam-frame.yml) rebuilds these files against unmodified repository inputs.

**Next exact proof:** define a source `Cfg` → `PhysicalWindow.Physical` simulation preserving source head position, all 18 local bits, and the remote tape, stopping at the first original left-list exhaustion or F/1 gate. The initial E3 source core corresponds to the `170 + 2048*r` painted-bit-zero prefix and an appropriate remote tape. Compose the verified `seed0_marker_safe` with that simulation to discharge `SourceMarkerSafe` without introducing any new finite closure. Then derive the unconditional, exact all-m prepared E first-event source theorem and apply it to a source-certified genuine blank section.
