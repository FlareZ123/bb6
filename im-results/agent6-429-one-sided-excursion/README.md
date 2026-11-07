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

[BB429SourceE1Return.lean](BB429SourceE1Return.lean) proves a further all-parameter theorem for the source `S_E` family. In the zipper convention, the left stack is nearest-cell first, the current cell is separate, and the right stack begins immediately to its right. The source configuration is

```lean
sourceScanE b suffix := z 4 (pairs01 b ++ ones 5) true suffix
```

with arbitrary finite right suffix. This is the same left/current pattern as the pinned Cryptids source's `cfg_ScanE` family; its right-hand parameters are subsumed by the arbitrary `suffix`. The physical left-to-right tape notation is `1^5(10)^b E>1`, because the zipper's left list is nearest-first.

After the first E/1 instruction, the head returns to the exact cell it just wrote. The formal theorem is `sourceScanE_e1_revisit`; at the return the machine is C scanning 1, and the audited C/1 row writes 0 on that cell. The number of additional steps after the initial E/1 instruction is

```
crossTime (2*k)   = 14*k + 41
crossTime (2*k+1) = 14*k + 15
```

The companion file [BB429SourceE1Delta.lean](BB429SourceE1Delta.lean) independently augments each raw zipper step with its signed head movement. It proves that the post-E/1 excursion has net displacement `+1`, while the initial E/1 instruction contributes `-1`. Thus the complete source-start run has net displacement exactly zero: the zipper head returns to its original coordinate. The six-step reduction has displacement `-4`, and the eight-step suffix-consumption macro has displacement `+4`; the two-step induction preserves the net `+1` for every b. This is the displacement-level companion to the configuration return theorem.

The final left stacks are also exact:

- even `b = 2*k`: `1^(4*k+1) ++ 0101 ++ 1^5`;
- odd `b = 2*k+1`: `1^(4*k+8)`.

The proof is a two-step induction. Its inductive step composes a six-instruction macro that removes two nearest `01` pairs while appending `1101` to the right suffix, the induction hypothesis with that extended suffix, and an eight-instruction macro that consumes the appended `1101`. The arbitrary-suffix quantifier is essential: it preserves the original written cell while the nested return is established.

This is a source-pattern-specific E/1 last-writer exclusion, not yet a theorem that every E/1 event on the genuine blank-origin orbit has this form. The broader (r=0,ldots,5) one-sided family discussed by Agent 32 still needs an exact representation-level comparison. The result is therefore retained in `im-results/`, and does not establish the blank-origin halting status.

**Source correspondence:** the source pattern is from the pinned upstream module [`M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA.lean`](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA.lean). The raw transition table is the same one already checked row-by-row in [`BB429SourceRows.lean`](BB429SourceRows.lean). The local proof was compiled under Lean 4.36.0-rc2; the axiom reports contain only `propext` and `Quot.sound`, with no `sorryAx`.

## Exact C/1 `finish_C_ScanE` head displacement

[`BB429FinishScanEDelta.lean`](BB429FinishScanEDelta.lean) adds the signed head displacement for the source `finish_C_ScanE` path. Its entry zipper is

```lean
finishCStart u p k :=
  z 2 (1 ++ 1^(2p) ++ (01)^u ++ 1^5) 1
    (1^6 ++ 1^(2k) ++ 01)
```

where the current symbol is shown separately and the right list begins immediately to its right. This is exactly the source C/1-state entry with left stack `1 ++ (11)^p ++ (01)^u ++ 1^5` and full right stack `1^7 ++ (11)^k ++ 01`.

The source path decomposes into two exact pieces:

1. A fixed 12-instruction C/1-to-A preparation. It preserves the left stack, rewrites the right prefix to the intermediate A configuration, and has net head displacement 0.
2. The source helper `shift_A_11 p`. Each two-instruction A/1,F/1 pair consumes the two nearest left-hand ones, appends one `01` pair after the two-cell right prefix, and moves the head left by exactly two cells. Induction gives total time (2p) and displacement (-2p).

The endpoint is exactly `cfg_Junc u (p+2) (2*k+1)`. The theorem `finishC_ScanE_delta` therefore gives

```lean
runWithDelta (12 + 2*p) (finishCStart u p k) =
  some (junc u (p+2) (2*k+1), -((2*p : Nat) : Int))
```

The companion `physical_finishC_ScanE_delta` instantiates Agent 32's generic `source_runWithDelta_rep` bridge. For every physical configuration representing the entry zipper, it proves the corresponding raw `target429` run reaches the physical endpoint and that its head is exactly the initial head minus (2p).

**Scope:** this is an exact endpoint/head-displacement certificate for the source macro, not a proof that the later path crosses the entire earlier `shift_E_11` interval. The remaining global argument must connect the parameters of the post-shift S_E return to this C/1 entry and prove the required coordinate inequality for the full swept block. The theorem by itself does not eliminate all E/1 last-writer candidates and does not establish any blank-origin halting result.

**Verification status:** the exact source dependency chain, including the real `BB429DeltaPhysicalBridge`, was compiled by the fail-closed [Junc crossing CI run 42394921817](https://github.com/FlareZ123/bb6/actions/runs/42394921817). The workflow audits the complete axiom output for `sorryAx`; none was found.

## Unbounded Junc-cycle crossing for both source return parities

`BB429JuncHeadExcursion.lean` now proves an all-parameter extension of the earlier fixed-offset return calculation.

For every affordable full cycle, the exact zipper transition is

```lean
runWithDelta (juncPosFullTime u 0 + (4*u+27)) (junc u 0 w) =
  some (junc (2*u+3) 0 (w-(2*u+3)), ((2*u+3 : Nat) : Int))
```

The positive parameter follows (U_{n+1}=2U_n+3), while the right-counter budget and head displacement both increase by (2U_n+3). The theorem `juncCycle_iter_delta` composes any number of affordable cycles exactly.

The bounded recursive search `juncTerminalN` finds the first unaffordable cycle. At that point the remaining counter (R=w-S_n) satisfies (R<2U_n+3). If (R\le4), the cycle endpoint already lies beyond the target. If (R\ge5), choosing (N=R/2-1) gives
- (1\le N\le U_n);
- (2N-1\le R), so the partial positive-u excursion is valid;
- (R-5<2N), so its head displacement crosses the target.

This is formalized by `juncCycle_crossing`: whenever the initial head offset (h) and right counter (w) satisfy (h+w=2k+5), some finite Junc run has displacement (d) with (2k<h+d).

The stronger theorem `junc_any_v_crossing` covers nonzero right-alternating parameter v as well. For any u≥1,w≥1 with h+w+2v=2k+5, it either normalizes a full cycle using `juncNormalize_delta` and invokes `juncCycle_crossing`, or uses a partial positive-u sweep directly. In the short-counter case w≤4, one step suffices; for w≥5, the choice N=w/2−1 gives the strict crossing.

The two source E/1 return parities satisfy this relation exactly:
- **Even branch:** the return reaches (J(2r+9,0,2k-6)) after displacement (11), for (k\ge3).
- **Odd branch:** the return reaches (J(2r+6,0,2k-2)) after displacement (7), for (k\ge1).

The theorems `sourceScanE_finishC_even_crosses_delta` and `sourceScanE_finishC_odd_crosses_delta` compose these prefixes with the cycle argument. Their physical lifts, `physical_sourceScanE_finishC_even_crosses_delta` and `physical_sourceScanE_finishC_odd_crosses_delta`, apply to every raw configuration representing the corresponding `sourceScanE` zipper. Each guarantees a later original-machine head position strictly greater than the starting head plus (2k).

**Scope:** this closes the unbounded head-crossing subproblem for these prepared source E/1 return families. It does not prove that any such prepared configuration is reached from the blank tape, and it does not decide the separate C/B `j_c_sweep` intermediate branches. In particular, `finishCStart` requires a C/1 tape with left word `true :: ones (2*p) ++ pairs01 u ++ ones 5` and right word `ones 6 ++ ones (2*k) ++ [false,true]`. The `j_c_sweep` endpoint has a different processed-pair history and can have only 0, 1 or 2 right-side ones in the intermediate (w=2u,2u+1,2u+2) cases. No direct tape adapter between those branches has been proved.

**Verification:** dedicated fail-closed workflow [`agent6-429-junc-crossing.yml`, run 42394921817](https://github.com/FlareZ123/bb6/actions/runs/42394921817) compiled the complete real source dependency chain through the all-parameter v=0 physical lifts. A second run [42395422632](https://github.com/FlareZ123/bb6/actions/runs/42395422632) compiled the nonzero-v normalization and `junc_any_v_crossing` extension. Both use `set -euo pipefail`, audit the complete axiom output for `sorryAx`, and completed successfully. The original broad `agent18-429-lastwriter.yml` workflow was also changed to fail closed, because its earlier tee pipelines could conceal Lean failures.

## Connection to the hard blank-origin question

Agent 32's [authentic halting biconditional](../agent32-429-raw-parent/README.md) identifies genuine source-blank C/01 as precisely fatal. Agent 18's [last-writer theorem](../agent18-429-lastwriter/README.md) proves that an actual fatal C/01 requires a one-sided excursion from a genuine left-moving write-one event D/0, E/1 or F/1, and gave one *synthetic* 18-step example. Our odd parametric family shows that such prepared-input excursions can persist for arbitrary left-block lengths in the **same** source machine, with a rigorous full-tape bridge.

This does not prove an authentic blank-root halt or nonhalt, a new BB(6) bound, or an externally novel mathematical result. The unbounded genuine-root condition is untouched. A successful next theorem must constrain the **full left-tape language on genuine blank-origin departures**, including any extra marks outside a short all-one block; the present examples are useful falsifiers for overstrong context-free claims.

## Separate finite local-language screen

The [visited-cell-aware `k`-factor saturation experiment](../agent6-429-regular-screen/README.md) exhaustively overapproximates reachable raw-tape factors for k=2 through 9. All those fixed points admit abstract non-record C/0 motifs, without any authentic blank witness. That result is independent of the parametric synthetic theorem and indicates that naive finite-factor joining loses decisive tape-history correlations. Neither finding justifies increasing a finite cutoff as a substitute for an actual-root invariant.

**Research objective:** obtain an all-time genuine-blank machine decision, possibly via a first-return grammar or physical state invariant that distinguishes authentic one-sided excursions from these source-valid prepared starts.
