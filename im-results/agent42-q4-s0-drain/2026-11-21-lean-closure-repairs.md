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

The full root import closure for `TM63GeneralQ4TerminalComposition.lean` remains uncompiled. It spans approximately 192 modules; the exported root theorem declarations and their transitive axiom/trust profiles have not been accepted. The next useful target is no longer the M1 bridge leaf: the bridge and its formerly failing carry-output dependency have since been repaired, but the exact parent source closure has not been compiled.

### Current M1 acceptance state

- `M1EvenValuationBridge.lean` has the reduced direct import slice `ChampionRootBridge`, `M1EvenState1Sweep`, `M1EvenState5Sweep`, `CountedSweep`, and `Lean.Elab.Tactic.Omega`. Agent 24 reports an exact Lean 4.36.0-rc2 local compile of the current bridge source (blob `32ba6984aae5428e5e0e316cc356042c039323f9`), with `m1EvenValuationBridge_run` profile `[propext, Quot.sound]` and no `sorryAx`.
- The distinct transitive dependency `im-results/agent24-champion-time/S1CarryOutputBridge.lean` failed in the only run of `m1-even-valuation-source.yml`, run `44910559991`, before the parent M1 module was reached. That failure is now stale: Agent 8 repaired the six reported errors and current main contains blob `67cc263caf04b53837c1e9a01ff0057a6435cda8`. The repaired declarations were locally compiled under Lean 4.36.0-rc2 against interface-equivalent stubs for `CountedSuffixOutput` and `CountedCarryLeftOutput`; their profiles are `d0pow_length: [propext, Quot.sound]`, `sideBit_d0pow_formula: [propext, Quot.sound]`, and `s1Config_decrement_leftOutput: [propext, Classical.choice, Quot.sound]`. No `sorryAx` remains in that stub preflight. It is not an exact-import compile.
- The parent `im-results/agent48-counted-inc0/M1EvenValuationSource.lean` (current blob `ed0d6cad465321acf86cb0b017d24088c192b989`) states the full source increment for every `0<n<2^L), after factoring `n=(2q+1)2^v`. Its public targets are `m1EvenValuation_q4_leftFacing`, `m1EvenValuation_q4_rightShape`, `m1EvenValuation_reset_prefix_source`, `m1EvenValuation_counted_increment_source_factorized`, and `m1EvenValuation_counted_increment_source`. Agent 24's static review found no substantive parameter/API mismatch, but the exact current import closure and these exported axiom profiles remain unverified.
- The focused manual-only `.github/workflows/m1-even-valuation-source.yml` is a materially narrower diagnostic gate than `middle34-acceptance`: it compiles only the exact M1 source import closure and checks those five public exports, whereas `middle34-acceptance` compiles five root modules and audits 14 integration exports. Keep this single focused gate for the M1 leaf; after it passes, use the existing `agent42-champion-terminal-source.yml` integration target. Both gates use the same RC2 toolchain and `tools/lean_compile_closure.py`; do not add another workflow or treat the old failed run as evidence against the repaired source. The focused workflow's axiom parser was also hardened: the previous version checked only the line containing the theorem name, which could miss `sorryAx` on continuation lines in Lean's wrapped `#print axioms` output. The current parser accumulates the complete bracketed profile, matches theorem names on identifier boundaries (so the factorized name cannot satisfy the un-factorized check), rejects incomplete reports, and includes a wrapped-`sorryAx` regression probe. Its parsing logic was exercised against a multiline synthetic report in the available JS runtime; no Lean workflow was dispatched.

`CountedResetBase.lean` has separately compiled with finite-trace `native_decide` certificates. The declarations are `resetBase_exact` (63/67/71-step traces), `resetBase_heads` (the corresponding finite head-containment checks), and `resetBase_frame` (which inherits them). Any final root trust report must expose generated native-computation dependencies for these declarations if they occur in the exact root closure; absence of `sorryAx` alone does not make them plain kernel-reduction proofs. The M1 counted-drain imports `CountedReset`, not `CountedResetBase`; do not attribute the latter's trust dependency to the M1 source without a dependency trace.

**Local runtime blocker (2026-11-21 15:14 UTC).** In this invocation, a fresh `container.exec` probe for `date -u` and the two mounted archive parts returned a tool-level `ClientError` before any shell output; prior `python.exec` probes also returned `ClientError`. No local Lean executable/version check or exact source compile was possible. This is an environment failure, not a Lean diagnostic. Do not dispatch CI as a substitute for the exact local preflight. The next useful action is to run `M1EvenValuationSource.lean` through `tools/lean_compile_closure.py` under Lean 4.36.0-rc2 in an invocation with a working local shell, inspect all five exported axiom profiles, and only then resume the exact root closure. Preserve the eight individually compiled modules above; do not repeat their unchanged checks.

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

**Archive integrity is unresolved across upload instances.** Agent 24 measured one invocation's concatenated parts at 568,438,050 bytes against a declared 608,393,640-byte member (39,955,590 bytes short, negative ZIP64 local-header offset; partial extraction had no `bin/lean`). Agent 44 measured a different current invocation's Files metadata at 608,393,796 bytes total, consistent with the 608,393,640-byte official tar.zst asset plus 156 bytes of ZIP metadata; Agent 44 explicitly cautions this may be a different upload instance. Neither report completed a CRC test or extraction. Therefore do not generalize Agent 24's shortfall to the attachments in this invocation: their integrity remains unverified. The required test is `unzip -t /tmp/lean.zip` before extraction. Independently, this invocation's `container.exec` and `python.exec` surfaces fail with tool-level `ClientError` before command execution. See [Agent 24's measurement](../../communications/broadcast/20261121T094511Z_agent24-tm63-preflight-blocker.md) and [Agent 44's upload-instance correction](../../communications/agent42/20261121T104127Z_agent44-rc2-size-and-extraction-correction.md).

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
