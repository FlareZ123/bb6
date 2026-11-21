# Authentic TM63 root: second q4Tail to S0 and one further recurrence

## Status

**The root-composition modules remain source-level drafts, not compiled or axiom-audited.** The authentic blank-root chain reaches the second q4Tail frame in `TM63RootQ4Tail.lean`. `P2RootS0FrameIdentity.lean` isolates the exact q4Tail-to-S0 frame identity and root specialization without importing the next-tail recurrence. `P2RootS0Identity.lean` is now a thin wrapper for the separate one-more-cycle recurrence. Independently, the direct terminal route in `im-results/agent42-q4-s0-drain/` bypasses the Type-C recurrence and has source-level `tm63_blank_halts` and `tm63_blank_attainable` theorem statements; its full import closure remains uncompiled. Three self-contained coordinate extracts, `NextResidualBranchExtract.lean`, `P2NextTypeCInputExtract.lean`, and `P2NextTypeCCheckpointExtract.lean`, previously compiled with Lean 4.36.0-rc2, but do not validate the root or terminal composition. None of this is an accepted full machine-run proof or a BB(6) upper bound.

## Recurrence-only tower sandwich: kernel-checked

A new standalone Lean module, [TM63TowerRecurrence.lean](TM63TowerRecurrence.lean), formalizes the moving-exponent inequalities from Agent 42's `TM63PublishedTowerSandwich.md`. It is deliberately a recurrence theorem, not a machine-execution theorem.

With paper indexing `T_1 = 2`, the module defines `tower n = T_(n+1)` and `V_0=63,` `V_(j+1)=2^V_j-1`. For every `j ≥ 2`, `tower_recurrence_bounds` proves exactly

[
T_{j+3}^{,T_{j+2}^{23/8}} < V_j
qquad	ext{and}qquad
V_j^{,T_{j+2}^{4092}} < T_{j+4}.
]

The rational lower exponent is represented integrally: the module proves that `T_(j+2)` has an exact integer eighth root, then represents its (23/8)-power as the 23rd power of that root. The proof uses only `import Lean` and the explicit recurrence. Local Lean 4.36.0-rc2 compilation succeeded; the exported axiom reports for the main theorem and induction step contain only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`, `unsafe`, or `native_decide`.

This formalizes the scale lemma only. It does not compile or validate `P2RootS0FrameIdentity.lean`, the direct terminal composition, the exact TM63 run, or any universal six-state upper bound. The latter source-level tasks remain open.

## Exact source construction

For arbitrary `z ≥ 1`, `w`, and `q`, put

- `a = 2^z - 1`,
- `n = 2^a`,
- `m = 3*2^z + 3*z + 7`,
- `tail0 = replicate 4 true ++ binDec w q ++ lh`,
- `tail = [1,0,0,1,1,1] ++ tail0.drop 6`,
- `ell = replicate (m+2) true ++ [0,1,0,0] ++ tail`.

The source tape `T2` is the authentic S0 drain output after the left sweep, the first four-step postlude frame, the 34-step second-cycle frame at head 1, and the two-zero setup at head `m+5`. The new source module states the three obligations required by Agent 42's generic `q4Tail_frame_eq_s0Config`:

1. `T2 (m+6) = true` (the second zero of the setup);
2. `T2 (m+5-i) = sideBit ell i` for every `i`;
3. `T2 (m+12+3*n+i) = false` for every `i`.

The residual decomposition is exact. The setup writes `m+5,m+6`; the E-scan and first left sweep give ones on `5..m+1); the S0 right stream supplies `m+2..m+4); and the 34-step frame marks `4`. The frame's in-window unmarked cells are blank, so cells `3,2,1,0` are `0100` and cells `-1..-6` are `100111`. For `x=-7-j`, the preceding frames and sweep preserve the original S0 left stream, whose side index reduces to `tail0[6+j]`; hence the remaining tail is exactly `tail0.drop 6`.

For the far-right ray, the original S0 right-facing word has length `6+3*n`. The first untouched cell after the q4Tail window has source index `3*n+11`, already beyond that finite word; all intervening frames, the two-zero setup, and the left sweep are local or preserve this ray. This gives the required blank right side.

## Draft theorem surface

`P2RootS0FrameIdentity.lean` contains:

- `q4TailS0SourceGuards`: the three source obligations and the `100` tail guard, for every (zge1,w,q);
- `q4TailS0Frame_eq_s0Config`: the generic frame identity
  `s0Config ell (n-1) (2^(n-1)-1) 0 (m+2+3*n)`;
- `tm63_root_second_q4Tail_eq_s0Config`: the authentic-root specialization using the exact P1 width and value.

`P2RootS0Identity.lean` now contains only:

- `q4TailS0Frame_to_nextQ4Tail`: one generic q4Tail-to-q4Tail recurrence with exact drain, P2 postlude, and next-prefix cost;
- `tm63_blank_reaches_next_q4Tail`: composition of the authentic blank-root path through the second q4Tail frame and one further recurrence.

The pointwise tape identity itself does not require oddness of (q); oddness is used by the existing root trajectory theorem to establish that the authentic run reaches the second-prefix frame.

## Direct terminal route (separate from the Type-C recurrence)

The direct route uses the authentic second-q4Tail frame, the frame-only S0 identity, the general-A S1 reparameterization, the counted drain, and the complete 24-class SectionResult dispatcher. It then reaches the terminal reset. It does **not** need the next-q4Tail recurrence, so it avoids the `111111` Type-C branch described below.

The source-level wrapper is `im-results/agent42-q4-s0-drain/TM63GeneralQ4TerminalComposition.lean`. Its theorem statements include `tm63_blank_halts` and `tm63_blank_attainable`. The exact conditional score has been reduced to a single weighted sum over the right-counter recurrence in `im-results/agent42-q4-s0-drain/SectionResultThreeCycle.md`. The arithmetic reductions are exact, but the root-to-terminal theorem composition and its full import closure remain uncompiled and unaudited.

## Iteration correction: the next residual is 111111

The one-step recurrence is not closed under its own type-A guard. After the P2 S0 drain/postlude and `firstCyclePrefix22`, the next q4Tail adapter sees residual tail

```lean
List.replicate 6 true ++ tail.drop 6
```

The first three ones are written by the marked cells of `firstCyclePrefix22End`; the next three come from old `tail[3..5]`, which are `111` for the root tail beginning `100111`. All later cells are old `tail[j]`. Thus the next residual begins `111111`, not `100`, so the existing `p2S0_to_next_q4Tail` theorem cannot simply be reapplied. The next postlude window is `11110000`, not its `00110000` type-A window.

This is now connected to the existing Type-C prefix. For `suffix = tail0.drop 6`, the k=0 case of `firstQ4P1Tail0_dropSixPlusSixK` gives a leading `1001` whenever the outer parameter `A≥3`. Agent42's residual map sends `100111 ++ suffix` to `111111 ++ suffix`. The subsequent P2 postlude frame at head `h=1` therefore has the exact Type-C input window `00 11111111 000`. The new `P2NextTypeCInputExtract.lean` proves this window; `P2NextTypeCCheckpointExtract.lean` proves every right-side guard required by `Agent24TypeCPrefix.typeCPrefix_from_checkpoint`: with `H=m+2+3*n` and `r=2^(n-1)` for the new S0 parameters, there are `H` ones, two zeros, `r` d1 blocks, and five terminating zeros. Thus the existing Type-C prefix applies at `h=1`, with Type-C parameters `(H,r)`, and returns a q4Tail frame at `g=H+7+3*r` after `H+3*r+77` steps.

The `11110000` branch is therefore no longer a dead end: it reaches the next q4Tail frame through the existing Type-C macro. The remaining gap is later in the cycle: identify that Type-C q4Tail frame's exact S0 left residual, apply the counted S0 drain and postlude, and prove that the next encoded `100` guard is exposed. Until that is proved, the arithmetic outer-counter identity is not yet an iterated machine recurrence, and no halting claim follows.

## Conditional material kept separate

`P2ActualBoundaryBridge.lean` and the 73-step `0101 1^7 00` branch concern a different conditional input family. They are preserved as independent finite-trace drafts and are **not** composed with `rootSecondQ4TailFrame`.

## Toolchain and trust status

Lean 4.36.0-rc2 was reconstructed locally from the concatenated split ZIP and used to compile `NextResidualBranchExtract.lean`, `P2NextTypeCInputExtract.lean`, and `P2NextTypeCCheckpointExtract.lean`. Their `#print axioms` reports contain only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`). These are self-contained extracts with normalized copies of the relevant source definitions, not a full repository import-closure build. A direct shallow `git clone` of the repository failed because DNS resolution for GitHub is unavailable in the local shell. No CI was dispatched as a substitute for full local preflight. `P2RootS0FrameIdentity.lean` and the direct terminal composition remain uncompiled; their axiom reports have not been executed. The recurrence wrapper `P2RootS0Identity.lean` is also uncompiled.

## Next work

1. When the local execution backend is available, compile `P2RootS0FrameIdentity.lean` first, then the exact direct terminal closure (`GeneralQ4TailS1Reparam.lean`, `GeneralQ4TailS1Config.lean`, `GeneralQ4TailTerminalComposition.lean`, and `TM63GeneralQ4TerminalComposition.lean`). Inspect all exported theorem axiom reports.
2. If the direct terminal route validates, use its exact one-dimensional score formula as a rigorous lower-bound candidate; do not promote it until the full source closure is compiler-accepted.
3. Compile `P2RootS0Identity.lean` separately only if the next-q4Tail recurrence is needed.
4. For the Type-C iterative branch, map its q4Tail output to exact S0 configuration, derive the left residual, and prove that the drain/postlude exposes the next `100` guard.
5. Independently pursue the universal six-state upper bound.

All work remains in `im-results/`. Nothing has been promoted to `results/`; BB(6) remains unresolved.
