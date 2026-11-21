# TM63 q4 Lean closure repairs — 2026-11-21

## Scope and status

This is an intermediate source-integration and proof-repair record, not a completed TM63 root proof or a BB(6) result. The target was `TM63GeneralQ4TerminalComposition.lean` under Lean 4.36.0-rc2.

## Directly compiled modules

The following eight modules were repaired and individually compiled locally. Their emitted `#print axioms` reports contained no `sorryAx`:

- `im-results/agent24-champion-time/CountedLBinDecHRun.lean`
- `im-results/agent48-counted-inc0/M0EvenEightValuationMacros.lean`
- `im-results/agent44-tm63-middle/SectionResultRunSource.lean`
- `im-results/agent44-tm63-middle/GeneralQ4TailArithmetic.lean`
- `im-results/agent48-counted-inc0/M0EvenEightValuationSweepFacts.lean`
- `im-results/agent48-counted-inc0/M0EvenFourQ4Bridge.lean`
- `im-results/agent48-counted-inc0/PositiveZSecondCycleBridge.lean`
- `im-results/agent48-counted-inc0/PositiveZFirstCycleBridges.lean`

Key fixes:
1. Corrected induction-hypothesis applications where the tape coordinate was fixed by induction and therefore was not an IH argument.
2. Made Nat subtraction occur before coercion to Int in sweep-coordinate identities.
3. Supplied normalized disequalities to simplification in exact tape-update proofs.
4. Imported `CountedReset` and opened its namespace in `SectionResultRunSource` for the actual `run_add` lemma.
5. Replaced unavailable Mathlib-only constructs with Lean-core alternatives (`Nat.strongRecOn`, `Nat.mul_lt_mul_of_pos_left`, explicit power positivity and finite arithmetic).
6. Corrected the exact ordered-list representation of finite configurations. Direct `fRun` evaluation confirmed that the 22-step and 34-step runs reached the expected state and head with the same written cells, but in a different list order. The 51-step M0 bridge had the same representation issue.

Five direct/transitive importers used `import Agent6Q4Prefix`, although the source module is `CountedQ4Prefix.lean` and retains namespace `BB6Coverage.Agent6Q4Prefix`. Those imports were changed to `CountedQ4Prefix`.

## Remaining blockers and next acceptance gate

The full root import closure for `TM63GeneralQ4TerminalComposition.lean` remains uncompiled. It spans approximately 192 modules; the current root theorem declarations and their transitive axiom profiles have not been accepted. The first actionable leaf remains `M1EvenValuationBridge.lean`, followed by its parent `M1EvenValuationSource.lean` and the remaining valuation/sweep modules.

The direct import slice of the current `M1EvenValuationBridge.lean` has already been reduced to:

- `ChampionRootBridge`
- `M1EvenState1Sweep`
- `M1EvenState5Sweep`
- `CountedSweep`
- `Lean.Elab.Tactic.Omega`

The former `CountedQ4Prefix` import and `Agent6Q4Prefix` namespace opening are absent from the current source. `E_scan` is supplied by `CountedSweep`, in the already-open `BB6Coverage.Agent48Champion` namespace. The smallest useful first preflight is therefore this target and its direct import closure, not the full 192-module root composition.

The next wrapper, `M1EvenValuationSource.lean`, additionally imports `M1EvenQ4Prefix`, `M1EvenQ4Suffix`, `Q4RightEndpoint`, `S1Encoder`, `S1CountedDrain`, and `CountedReset`. Once the bridge is accepted, compile this wrapper and then resume the exact root closure. Preserve the eight individually compiled modules listed above; do not repeat their unchanged checks.

`CountedResetBase.lean` has separately compiled with finite-trace `native_decide` certificates. The source declarations containing them are `resetBase_exact` (the 63/67/71-step finite traces) and `resetBase_heads` (the corresponding finite head-containment checks); `resetBase_frame` inherits these dependencies. Any final exported-axiom/trust report must expose the generated `native_decide` dependencies for all three declarations explicitly; absence of `sorryAx` alone does not make them plain kernel-reduction proofs.

**Local runtime blocker (2026-11-21 10:34 UTC).** An invocation of `container.exec` with the trivial command `echo runtime-check && ls -l /mnt/data/lean-4.36.0-rc2-linux.zip.001 /mnt/data/lean-4.36.0-rc2-linux.zip.002 && date -u` returned a tool-level `ClientError` before producing any shell output. The earlier `python.exec` attempt in this invocation also returned `ClientError`. No Lean executable/version check or Lean compiler diagnostic was obtained. This is an execution-environment failure, not evidence of a Lean source error. No CI was dispatched as a substitute. Archive integrity is also unverified: Agent 44 reports that a different/current upload instance had two parts of 304,196,898 bytes each (total 608,393,796), only 156 bytes larger than the official 608,393,640-byte inner tar.zst asset, consistent with a complete outer ZIP but not a CRC test. This may not be the same upload instance as earlier truncation reports; the current conversation Files listing exposes no byte sizes. Do not claim the present archive is truncated or intact without running `unzip -t`. The intended sequence is outer ZIP extraction followed by `tar --zstd -xf` on the inner tar.zst.

Until a working local shell is available, do not expand the score derivations or claim source acceptance. The next action is to reconstruct and verify Lean 4.36.0-rc2 locally, compile the narrow M1 bridge slice above, print its exported axiom profiles, then continue through the parent and exact root closure.

## Reproduction details

### Lean 4.36.0-rc2 bootstrap

The two uploaded files are split parts of an outer ZIP. Reconstruct and test that ZIP, extract its inner tar.zst, then expose the Lean binary:

```sh
mkdir -p /tmp/lean
cat /mnt/data/lean-4.36.0-rc2-linux.zip.{001,002} > /tmp/lean.zip
unzip -t /tmp/lean.zip
unzip -q /tmp/lean.zip -d /tmp/lean
tar --zstd -xf /tmp/lean/lean-4.36.0-rc2-linux.tar.zst -C /tmp/lean
export PATH="/tmp/lean/lean-4.36.0-rc2-linux/bin:$PATH"
lean --version
```

**Archive integrity is no longer unknown.** Agent 24 measured the concatenated uploaded parts at 568,438,050 bytes, while the ZIP declares a 608,393,640-byte stored member: a 39,955,590-byte shortfall, with a negative ZIP64 local-header offset. Partial extraction produces no `bin/lean`. See [the concrete blocker report](../../communications/broadcast/20261121T094511Z_agent24-tm63-preflight-blocker.md). Do not retry the same two parts or treat the resulting extraction as a compiler failure. A complete RC2 archive is required. Independently, this invocation's `container.exec` and `python.exec` surfaces fail with tool-level `ClientError` before command execution.

### First narrow preflight

The smallest useful first target is `M1EvenValuationBridge.lean`. Stage and compile the exact current-main sources in this order:

1. `im-results/agent8-coverage-contract/Frontier.lean`
2. `im-results/agent8-coverage-contract/Symmetry.lean`
3. `im-results/agent8-coverage-contract/RootShift.lean`
4. `im-results/agent48-champion-root/ChampionRootBridge.lean`
5. `im-results/agent48-root-witness/M1EvenState1Sweep.lean`
6. `im-results/agent24-champion-time/M1EvenState5Sweep.lean`
7. `im-results/agent24-champion-time/CountedSweep.lean`
8. `im-results/agent48-counted-inc0/M1EvenValuationBridge.lean`

The preferred reproducible local command (after the Lean 4.36.0-rc2 bootstrap succeeds) is:

```sh
python3 tools/lean_compile_closure.py \
  im-results/agent48-counted-inc0/M1EvenValuationBridge.lean \
  --workdir /tmp/tm63-m1-bridge \
  --jobs 8
```

This runner resolves the import graph and emits the source's `#print axioms` output; retain the first concrete compiler diagnostic and full output. If this slice passes, compile `M1EvenValuationSource.lean` next with the same runner: Its additional direct imports (beyond `M1EvenValuationBridge`) are:

- `M1EvenQ4Prefix` — `im-results/agent48-counted-inc0/M1EvenQ4Prefix.lean`
- `M1EvenQ4Suffix` — `im-results/agent42-champion-terminal/M1EvenQ4Suffix.lean`
- `Q4RightEndpoint` — `im-results/agent24-champion-time/Q4RightEndpoint.lean`
- `S1Encoder` — `im-results/agent8-s1-encoder/S1Encoder.lean`
- `S1CountedDrain` — `im-results/agent48-counted-inc0/S1CountedDrain.lean`
- `CountedReset` — `im-results/agent8-counted-reset/CountedReset.lean`
- `Lean.Elab.Tactic.Omega`

Important scope distinction: the bridge-only import reduction removes `CountedQ4Prefix` from `M1EvenValuationBridge` itself, but the parent `M1EvenValuationSource` still reaches `CountedQ4Prefix` through both `M1EvenQ4Prefix` and `Q4RightEndpoint`. Do not infer that the whole parent closure has shed this dependency. Its preferred preflight command is:

```sh
python3 tools/lean_compile_closure.py \
  im-results/agent48-counted-inc0/M1EvenValuationSource.lean \
  --workdir /tmp/tm63-m1-source \
  --jobs 8
```

Compile the parent closure after the bridge preflight, then resume the exact root closure below.

### Full root closure

Lean 4.36.0-rc2 is required. For the terminal source, extract `TerminalProofs.tar.xz.b64` first, then decode `TerminalLeftExact.lean.xz.b64` over `TerminalLeft.lean`; reversing this order overwrites the exact left proof with the older archived checkpoint.

The terminal support modules must first be reconstructed into `/tmp/a42-terminal`, then supplied as an additional source root. The exact staging command is:

```sh
mkdir -p /tmp/a42-terminal
python3 - <<'PY'
import base64, io, lzma, pathlib, tarfile
root = pathlib.Path('/tmp/a42-terminal')
archive = pathlib.Path('im-results/agent42-champion-terminal/TerminalProofs.tar.xz.b64')
data = base64.b64decode(archive.read_text())
tarfile.open(fileobj=io.BytesIO(data), mode='r:xz').extractall(root, filter='data')
compressed = pathlib.Path('im-results/agent42-champion-terminal/TerminalLeftExact.lean.xz.b64')
(root / 'TerminalLeft.lean').write_bytes(lzma.decompress(base64.b64decode(compressed.read_text())))
PY
cp im-results/agent42-champion-terminal/TerminalBridge.lean /tmp/a42-terminal/
```

The current root target is:

```sh
python3 tools/lean_compile_closure.py \
  im-results/agent42-q4-s0-drain/TM63GeneralQ4TerminalComposition.lean \
  --workdir /tmp/tm63-general-q4-closure \
  --source-root /tmp/a42-terminal \
  --jobs 8 \
  --override TerminalBridge=im-results/agent42-champion-terminal/TerminalBridge.lean
```

The final audit must retrieve exactly one exported axiom/trust profile for each of:
`tm63_blank_reaches_general_q4_terminal`,
`tm63_general_q4_terminalSectionBits`,
`tm63_blank_halts`, and
`tm63_blank_attainable`.
Any transitive `native_decide` dependencies (notably the repaired `CountedResetBase` finite traces if they occur in this closure) must be reported explicitly, not described as plain kernel reduction.

### Existing manual workflow boundary

The existing `.github/workflows/agent42-champion-terminal-source.yml` target `middle34-acceptance` is **not** an acceptance proxy for `TM63GeneralQ4TerminalComposition.lean`. It compiles the five roots `M1EvenValuationSource`, `M2EvenSixGenericCounted`, `TM63RootMiddle34`, `TM63RootAfterSectionResultToOne`, and `Q4S0FirstCycleMacros`, and audits their 14 middle-34 exports. It does not compile the direct arbitrary-`A` q4Tail/S0 composition or its `P2RootS0FrameIdentity` dependency. After the local preflight succeeds, extend this same manual workflow with a named target for the exact `TM63GeneralQ4TerminalComposition` closure and its four exports; do not create a new workflow or dispatch `middle34-acceptance` as a substitute.
