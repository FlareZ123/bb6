# Two-frontier finite-window screen of the 663 historical BB(6) holdouts

**Scope (7 November 2026): finite abstract-model negative experiment.** A sound-by-construction, head-centred tape-window overapproximation with two saturated *visited-head frontiers* admits a possible halting path for **each of the 663 machines** in [the frozen 16 October 2026 holdout input](../../resources/BB6_holdouts_663_2026-10-16.txt), at window radius seven. **No machine was decided, no genuine halt witness was obtained, and no BB(6) bound improved.** This experiment is preserved in `im-results/` as a reproducible warning against treating a small finite-window quotient as an all-time certificate.

## Abstract domain and simulation argument

For radius `r`, a state records a control state `q∈{A,…,F}`, the `2r+1` tape bits at offsets `[-r,r]` around the actual head, and two distances: `min(head−L,r+1)` and `min(R−head,r+1)`, where `L,R` are the extreme tape coordinates *ever scanned* by the head. The blank initial state has control A, zero bits, and both distances zero. These distances are not tape-cell ages or the locations of the extreme nonzero cells.

For each ordinary instruction the center bit is overwritten, the window shifts, and a newly exposed boundary cell is forced zero **if it lies outside the previously scanned span**. If it might have been scanned earlier, both possible bits are allowed. A saturated distance `r+1` decreases on an inward move nondeterministically to `r` or remains `r+1`. Unsaturated distances update exactly, including extension of a fresh frontier.

**Soundness rationale:** Inductively map every concrete blank-run configuration to the abstract control, exact local window, and saturated visited span. Every concrete step has an abstract successor, because its incoming bit and updated distances are among the listed possibilities. Therefore an *exhaustive abstract reachable closure with no halting slot* would imply concrete nonhalting. We did **not** obtain such a closure on this corpus. A reachable abstract halt is at most a spurious possibility and supplies no evidence that a real Turing machine halts. This relation is explained mathematically here; it has **not** been independently formalized in Lean.

## Reproduction and observed outcome

The read-only [CommonJS scanner](../../tools/two-frontier-window.cjs) parses all six input rows as literal two-symbol actions, explores the finite abstract state graph breadth-first, reuses visit-tag memory between machines, and reports explicit `abstract-halt`, `abstract-safe`, or `cap` statuses. Its default input is the preserved 663-line file, default radius is seven, and default per-machine generated-state cap is 400,000. The source supports radius 0 to 7. A cap is explicitly inconclusive; it is never silently converted into a proof.

The full-corpus radius-seven run completed **without caps**:

| Measurement | Outcome |
| --- | ---: |
| Frozen rooted-machine inputs | 663 |
| Abstract halting paths | 663 |
| Abstract-safe closures | 0 |
| Cap exhaustions | 0 |
| Smallest first abstract-halt depth | 24 |
| Largest first abstract-halt depth | 166 |
| Most visited before first abstract halt | 261,286 |

The most costly machine was `1RB0LF_0RC0RB_1LC1LD_1RE0RD_---0RA_1LA0LF`, with 261,286 states dequeued, 269,985 generated, and first abstract halt at BFS depth 68. The intermediate radius-two through radius-six screens also produced an abstract halt for all 663 inputs, with no caps; the radius-seven complete sweep and the hardest sample were independently reproduced using a local C++ BFS with the same transition relation. The read-only JS scanner was locally exercised on machine #429 and the maximal case: both returned `abstract-halt`, and the maximal case reproduced its visited/generated counts.

For the exact source-root #429 `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`, the first radius-seven abstract halt occurs at depth **59**. The genuine physical all-time stopping event is the [source-certified B/001 gate](../agent32-429-raw-parent/README.md). The abstract path is not an occurrence of B/001 on the real tape. A head-window invariant that loses the order and content of cells beyond radius seven cannot certify this root using this quotient alone.

## Limitations and next useful distinction

These results rule out **this particular radius-seven graph closure** for the frozen corpus. They do not rule out larger radii, different abstract transition semantics, regular-language invariants, preserved tape-history, or exact Poincaré-return proofs. For #429, a valuable next step is to relate a true blank-origin source section to a history-sensitive physical tape language that excludes the B/001 event. Increasing the window without recording the long-range history should be justified by a targeted counterexample to an earlier spurious abstract path.

This is a tool and negative experiment. It is **not** a publication-level positive BB(6) theorem, and belongs exclusively under `im-results/`.
