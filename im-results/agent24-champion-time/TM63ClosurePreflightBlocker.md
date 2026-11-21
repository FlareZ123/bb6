# TM63 exact-source preflight blocker (Agent 24, 2026-11-21)

## Status

The target remains `im-results/agent42-q4-s0-drain/TM63GeneralQ4TerminalComposition.lean`. Its approximately 192-module transitive closure has not been compiled or axiom-audited in this invocation. No exact TM63 blank-start halting-time theorem is claimed.

The Critic's 09:34 UTC direction is to freeze further score/tower refinements and close this source-acceptance gate. The existing conditional score work is preserved elsewhere in `im-results/`; it is not advanced here.

## Concrete local toolchain failure

The supplied split archive is truncated, not a valid RC2 installation:

- `lean-4.36.0-rc2-linux.zip.001` + `.002` concatenate to 568,438,050 bytes.
- The ZIP central directory declares one stored member with both compressed and uncompressed sizes 608,393,640 bytes.
- The concatenation is therefore short by 39,955,590 bytes; Python's ZIP metadata also reports a negative ZIP64 local-header offset.
- Extraction produced only `LICENSE`, `share/`, and `lib/`; there is no `bin/lean` or `bin/lake`. Zstd/unzip report corruption.
- The official RC2 Linux tar.zst asset is 608,393,640 bytes, but direct recovery through the available download path was blocked by the URL-view restriction. The exact release URL was provided in the conversation.

Consequently this invocation cannot run `lean --version`, compile a module, or report an axiom profile. This is a toolchain blocker, not evidence for or against any Lean source declaration.

## Smallest named source slice to resume first

The first named remaining source blocker is:

`im-results/agent48-counted-inc0/M1EvenValuationBridge.lean`

Its direct imports are exactly:

- `ChampionRootBridge`
- `M1EvenState1Sweep`
- `M1EvenState5Sweep`
- `CountedQ4Prefix`
- `Lean.Elab.Tactic.Omega`

The bridge is 523 lines and contains no textual `sorry`, `admit`, `axiom`, `unsafe`, or `native_decide` markers. This is only a source scan, not a compile result. Agent 38's two coordinate/setup rewrites are already present in the current file (the recursive state-5 coordinate rewrite and the right-ones setup-cell rewrite); they remain uncompiled.

The smallest useful preflight after obtaining a complete RC2 toolchain is therefore:

1. Compile `M1EvenValuationBridge.lean` with its five direct imports, allowing the compiler to expose the first failing transitive dependency.
2. Fix the first actual diagnostic and compile this slice before expanding.
3. Then run the existing closure script against `TM63GeneralQ4TerminalComposition.lean` with the already documented `TerminalBridge` override.
4. Obtain exported axiom profiles for the final root/attainability declarations, explicitly disclosing any generated `native_decide` dependencies in the transitive reset-base path.

The eight individually compiled modules listed in `im-results/agent42-q4-s0-drain/2026-11-21-lean-closure-repairs.md` should be reused, not recompiled as independent tasks. `CountedResetBase` parses/compiles but its finite-trace proofs use `native_decide`; that distinction must remain visible in the trust report.

## Next action

Obtain an intact `lean-4.36.0-rc2-linux.tar.zst` (or reuse another agent's exact RC2 runtime), then compile the M1 slice first. Do not dispatch CI before the exact local preflight succeeds.