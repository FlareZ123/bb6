# Authentic TM63 root: second q4Tail to S0 and one further recurrence

## Status

**The root-composition modules remain source-level drafts, not compiled or axiom-audited.** The authentic blank-root chain currently reaches the second q4Tail frame in `TM63RootQ4Tail.lean`. `P2RootS0Identity.lean` supplies the pointwise q4Tail-to-S0 interface and composes one further q4Tail recurrence. A separate self-contained coordinate extract, `NextResidualBranchExtract.lean`, has now compiled with Lean 4.36.0-rc2; it does not compile the root module's import closure. This is not an accepted full machine-run proof, not a halt proof, and not a BB(6) upper bound.

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

`P2RootS0Identity.lean` contains:

- `q4TailS0SourceGuards`: the three source obligations and the `100` tail guard, for every `z ≥ 1,w,q`;
- `q4TailS0Frame_eq_s0Config`: the generic frame identity
  `s0Config ell (n-1) (2^(n-1)-1) 0 (m+2+3*n)`;
- `tm63_root_second_q4Tail_eq_s0Config`: the authentic-root specialization using the exact P1 width and value;
- `q4TailS0Frame_to_nextQ4Tail`: one generic q4Tail-to-q4Tail recurrence with exact drain, P2 postlude, and next-prefix cost;
- `tm63_blank_reaches_next_q4Tail`: composition of the authentic blank-root path through the second q4Tail frame and one further recurrence.

The pointwise tape identity itself does not require oddness of `q`; oddness is used by the existing root trajectory theorem to establish that the authentic run reaches the second-prefix frame. The new recurrence then uses the corrected `100` tail guard.

## Iteration correction: the next residual is 111111

The one-step recurrence is not closed under its own type-A guard. After the P2 S0 drain/postlude and `firstCyclePrefix22`, the next q4Tail adapter sees residual tail

```lean
List.replicate 6 true ++ tail.drop 6
```

The first three ones are written by the marked cells of `firstCyclePrefix22End`; the next three come from old `tail[3..5]`, which are `111` for the root tail beginning `100111`. All later cells are old `tail[j]`. Thus the next residual begins `111111`, not `100`, so the existing `p2S0_to_next_q4Tail` theorem cannot simply be reapplied. The next postlude window is `11110000`, not its `00110000` type-A window. See `NextResidualBranch.md` for the coordinate derivation and `NextResidualBranchExtract.lean` for the self-contained Lean proof.

This also corrects the planned outer-counter integration: `firstQ4P1Tail0_dropSixPlusSixK` is an arithmetic list identity; the present one-step machine composition does not prove that the machine exposes successive `tail0.drop(6+6*k)` guards. A separate source-level `11110000` branch is required before claiming iterative A-to-A-2 progress.

## Conditional material kept separate

`P2ActualBoundaryBridge.lean` and the 73-step `0101 1^7 00` branch concern a different conditional input family. They are preserved as independent finite-trace drafts and are **not** composed with `rootSecondQ4TailFrame`.

## Toolchain and trust status

Lean 4.36.0-rc2 was reconstructed locally from the concatenated split ZIP and used to compile `NextResidualBranchExtract.lean`. Its `#print axioms next_tail_cells` output is `[propext, Classical.choice, Quot.sound]` (no `sorryAx`). This is a self-contained extract with normalized copies of the relevant source definitions, not a full repository import-closure build. A direct `git clone` of the repository failed because DNS resolution for GitHub is unavailable in the local shell. No CI was dispatched as a substitute for full local preflight. `P2RootS0Identity.lean` and its full import closure remain uncompiled; its axiom reports have not been executed.

## Next work

1. When a local execution backend works, run the corrected Lean 4.36.0-rc2 bootstrap and compile the exact import closure of `P2RootS0Identity.lean`; fix the first compiler diagnostic, then inspect all exported theorem axiom reports.
2. Independently review the residual indices and right-ray bound, especially the `tail0.drop 6` side-bit reduction and the frame-window coordinates.
3. Prove the exact source transition for the `11110000` branch arising after the one-step recurrence. Determine whether it consumes the next encoded d0 blocks and restores a `100` guard, or enters a terminal SectionBits/Type-C family. Only then connect the arithmetic outer-counter descent to an actual trajectory.
4. Prove the resulting trajectory halts and obtain its exact runtime; separately pursue the universal six-state upper bound.

All work remains in `im-results/`. Nothing has been promoted to `results/`; BB(6) remains unresolved.
