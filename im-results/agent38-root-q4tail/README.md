# Authentic TM63 root: second q4Tail to S0 and one further recurrence

## Status

**Source-level Lean draft; not compiled or axiom-audited.** The authentic blank-root chain currently reaches the second q4Tail frame in the existing source draft `TM63RootQ4Tail.lean`. The new `P2RootS0Identity.lean` supplies the missing pointwise q4Tail-to-S0 interface and composes one further q4Tail recurrence. This is a substantive proof draft, not an accepted Lean result, not a halt proof, and not a BB(6) upper bound.

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

## Conditional material kept separate

`P2ActualBoundaryBridge.lean` and the 73-step `0101 1^7 00` branch concern a different conditional input family. They are preserved as independent finite-trace drafts and are **not** composed with `rootSecondQ4TailFrame`.

## Toolchain and trust status

No local Lean command ran in this invocation: the available Python/container execution calls failed at the tool boundary before executing commands. The latest Critic handoff corrects the archive recipe: the concatenated split ZIP contains an inner `lean-4.36.0-rc2-linux.tar.zst`; after unzipping, extract it with `tar --zstd -xf /tmp/lean/lean-4.36.0-rc2-linux.tar.zst -C /tmp/lean`, then add the extracted `bin` directory to `PATH`. This correction is reported from another working shell and was not independently tested here. No CI was dispatched as a substitute for local preflight. The source and its full import closure remain uncompiled; the `#print axioms` commands in the file have not been executed.

## Next work

1. When a local execution backend works, run the corrected Lean 4.36.0-rc2 bootstrap and compile the exact import closure of `P2RootS0Identity.lean`; fix the first compiler diagnostic, then inspect all exported theorem axiom reports.
2. Independently review the residual indices and right-ray bound, especially the `tail0.drop 6` side-bit reduction and the frame-window coordinates.
3. Integrate the next q4Tail frame with the existing outer-counter descent. Determine and prove the updated residual parameterization until the A=1 Type-C and A=2 terminal cases are reached.
4. Prove the resulting trajectory halts and obtain its exact runtime; separately pursue the universal six-state upper bound.

All work remains in `im-results/`. Nothing has been promoted to `results/`; BB(6) remains unresolved.
