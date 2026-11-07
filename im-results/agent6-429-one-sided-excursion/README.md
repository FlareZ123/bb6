# #429: original-physical odd/even synthetic one-sided excursions

**Research status (7 November 2026): original-repository-source Lean 4.36.0-rc2 verified, intermediate only.** The authentic blank-start halting status of the six-state machine `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA` remains unknown. This dossier proves unbounded families of *prepared-input* trajectories and a whole-tape simulation bridge. It supplies a rigorous test family for proposed genuine-root right-boundary invariants. A prepared tape cannot be silently substituted for the blank tape.

## Exact original-source theorem

Let `M = BB429PhysicalFrontier.target429`, the unchanged source-defined six-state, two-symbol physical machine with a bi-infinite tape, and define `sourcePrepared n` by:

- current state **E**, head coordinate 0, currently scanning 0;
- symbols 1 at the consecutive left positions `-n,...,-1`;
- symbol 1 at coordinate `+1`;
- zero at every remaining coordinate.

The source-verified [`BB429PhysicalBridge.lean`](BB429PhysicalBridge.lean) establishes for every `k:Nat`:

```lean
BB429PhysicalBridge.odd_original_source_halts (k : Nat) :
  BB6Coverage.run target429 (2*(2*k+3)+14)
    (sourcePrepared (2*k+3)) = none
```

More precisely, the genuine raw run from `sourcePrepared (2*k+3)` reaches a configuration **C scanning zero with a marked right neighbor** after exactly `2*(2*k+3)+12` successful physical steps. One further real instruction enters D scanning one, and the next query halts. Hence the very first unproved extra requirement for the genuine blank run is whether it can ever create this complete prepared tape, or some related fatal one-sided excursion.

The contrasting even family `sourcePrepared (2*k+2)` genuinely reaches **C scanning one** after `2*(2*k+2)+3` successful source steps, as certified by `even_original_source_at_boundary`. This is a distinct nonfatal observation at that time, **not** a proof that the even prepared machine never halts later.

For any finite left-inspection width `w`, the two prepared inputs with lengths `2w+3` and `2w+4` have exactly the same first `w` left symbols. Their above certified outcomes differ, with the odd one explicitly fatal. This shows why only a bounded, unannotated left-marked prefix cannot explain these particular synthetic returns. It does **not** refute every possible finite automaton or local proof rule, since parity is regular and other global context can matter.

## Complete-tape proof chain

[`BB429OddExcursion.lean`](BB429OddExcursion.lean) implements a finite binary zipper simulator and inductively proves two exact run macros:

- `odd_prepared_fatal` at time `2*(2k+3)+12`;
- `even_prepared_crosses` at time `2*(2k+2)+3`.

The proofs handle every natural `k` and every repeated two-cell burst; no fixed-depth simulation is extrapolated. [`BB429SourceRows.lean`](BB429SourceRows.lean) compiles the original repository `target429` and proves `action_matches_target` for **all 12** state-symbol rows.

The new original-physical bridge defines `Represents zipper physical` as equality of the state, currently scanned symbol, and **every** left and right tape symbol at every natural distance from the physical head, with missing zipper symbols interpreted as zeros. `rightRep` and `leftRep` show exact preservation of this unbounded tape relation under either ordinary move. `sim_one` matches a zipper step with the original machine's `rawStep`; `source_run_rep` inducts over arbitrary run length and bridges step-first zipper recursion to the repository's step-last physical `run`. `source_prepared_rep` establishes the initial tape correspondence for **all** integer coordinates. Composition yields the two original-machine event theorems and the odd-source halting theorem.

**Verification:** unchanged-original-source [manual GitHub Actions run 42344559326](https://github.com/FlareZ123/bb6/actions/runs/42344559326) passed at commit `d6a8b451e17f0b216cc8f75b249de29efa944334` under Lean 4.36.0-rc2, via the previously established manual-only `.github/workflows/agent18-429-lastwriter.yml`. The workflow builds the full earlier Agent 8, Agent 32, Agent 1 and Agent 18 dependencies and these three new files, and rejects `sorryAx`. The axiom reports for the physical bridge are restricted to ordinary `[propext, Classical.choice, Quot.sound]` or smaller subsets. The local cross-check compiled against an exact matching interface before the source run. No custom proof axioms are introduced.

## Exact source S_E E/1 return theorem

[BB429SourceE1Return.lean](BB429SourceE1Return.lean) proves a further all-parameter theorem for the source `S_E) family. In the zipper convention, the left stack is nearest-cell first, the current cell is separate, and the right stack begins immediately to its right. The source configuration is

```lean
z 4 ((01)^b ++ 1^5) true suffix
```

with arbitrary finite right suffix. This is the same left/current pattern as the pinned Cryptids source's `cfg_ScanE` family; its right-hand parameters are subsumed by the arbitrary `suffix`. The physical left-to-right tape notation is `1^5(10)^b E>1`, because the zipper's left list is nearest-first.

After the first E/1 instruction, the head returns to the exact cell it just wrote. The formal theorem is `sourceScanE_e1_revisit`; at the return the machine is C scanning 1, and the audited C/1 row writes 0 on that cell. The number of additional steps after the initial E/1 instruction is

```
crossTime (2*k)   = 14*k + 41
crossTime (2*k+1) = 14*k + 15
```

The final left stacks are also exact:

- even `b = 2*k`: `1^(4*k+1) ++ 0101 ++ 1^5`;
- odd `b = 2*k+1`: `1^(4*k+8)`.

The proof is a two-step induction. Its inductive step composes a six-instruction macro that removes two nearest `01` pairs while appending `1101` to the right suffix, the induction hypothesis with that extended suffix, and an eight-instruction macro that consumes the appended `1101`. The arbitrary-suffix quantifier is essential: it preserves the original written cell while the nested return is established.

This is a source-pattern-specific E/1 last-writer exclusion, not yet a theorem that every E/1 event on the genuine blank-origin orbit has this form. The broader (r=0,ldots,5) one-sided family discussed by Agent 32 still needs an exact representation-level comparison. The result is therefore retained in `im-results/`, and does not establish the blank-origin halting status.

**Source correspondence:** the source pattern is from the pinned upstream module [`M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA.lean`](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA.lean). The raw transition table is the same one already checked row-by-row in [`BB429SourceRows.lean`](BB429SourceRows.lean). The local proof was compiled under Lean 4.36.0-rc2; the axiom reports contain only `propext` and `Quot.sound`, with no `sorryAx`.

## Connection to the hard blank-origin question

Agent 32's [authentic halting biconditional](../agent32-429-raw-parent/README.md) identifies genuine source-blank C/01 as precisely fatal. Agent 18's [last-writer theorem](../agent18-429-lastwriter/README.md) proves that an actual fatal C/01 requires a one-sided excursion from a genuine left-moving write-one event D/0, E/1 or F/1, and gave one *synthetic* 18-step example. Our odd parametric family shows that such prepared-input excursions can persist for arbitrary left-block lengths in the **same** source machine, with a rigorous full-tape bridge.

This does not prove an authentic blank-root halt or nonhalt, a new BB(6) bound, or an externally novel mathematical result. The unbounded genuine-root condition is untouched. A successful next theorem must constrain the **full left-tape language on genuine blank-origin departures**, including any extra marks outside a short all-one block; the present examples are useful falsifiers for overstrong context-free claims.

## Separate finite local-language screen

The [visited-cell-aware `k`-factor saturation experiment](../agent6-429-regular-screen/README.md) exhaustively overapproximates reachable raw-tape factors for k=2 through 9. All those fixed points admit abstract non-record C/0 motifs, without any authentic blank witness. That result is independent of the parametric synthetic theorem and indicates that naive finite-factor joining loses decisive tape-history correlations. Neither finding justifies increasing a finite cutoff as a substitute for an actual-root invariant.

**Research objective:** obtain an all-time genuine-blank machine decision, possibly via a first-return grammar or physical state invariant that distinguishes authentic one-sided excursions from these source-valid prepared starts.
