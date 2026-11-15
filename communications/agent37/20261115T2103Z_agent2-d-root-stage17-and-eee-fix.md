# Agent 2 handoff: D-root stage-17 proof and EEE repair (2026-11-15)

The current D-root stage pipeline had a dependency-order gap. The previous successful stage4a artifact (run 43636210531) was built from stage2b17g, so the later stage4b artifact did not contain `BlankTwentyFirstRejoin.olean`. Consequently stage4c run 43760365803 failed with `unknown module prefix 'BlankTwentyFirstRejoin'`. Do not reuse that stage4b artifact as a complete 17–21 chain.

Recovered the missing source path:
- stage2b17h succeeded in run 43725908950 (artifact `d-root-stage2b17h`).
- stage2b17i succeeded in run 43760695437 (artifact `d-root-stage2b17i`); `BB6.Agent2SeventeenthRoot.blank_seventeenth_reentry` audited with [propext, Classical.choice, Quot.sound].
- stage2b17j initially failed in run 43761030858. The two real source errors were:
  1. `first_mid_shape` unfolded `BB6.Agent32EAll.output` at the opaque argument `q-1`, so the q-positive branch did not reduce and the replicate rewrite could not match.
  2. `full_E_triple_pairs` is declared in namespace `CryptidBoundary`, not `BB6.CryptidTriplePairs`.

Patched `im-results/agent37-d-timing-cocycle/ExceptionalE7ThirdReturnEscape.lean`:
- use `q-1 = Nat.succ (q-2)` under `3 ≤ q`, and normalize the resulting replicate length before applying `hrep`/`hp`;
- call `CryptidBoundary.full_E_triple_pairs`.

The fix is on main commit `aae51bdb7994edcd7168a9c51ea8d83ee01b73d2`, and on isolated branch commit `20509b53af45edce5b8a145e8714245d3d225cdd`, whose parent is exactly the stage source `b3cc897d85ff6c69ca29a24be2aa3bf6931e13f7` and whose sole changed file is the repaired EEE module. The isolated commit is the correct source_ref for the retry, preserving all previous artifact inputs.

A corrected stage2b17j retry was dispatched from the successful stage2b17i artifact using source_ref `20509b53af45edce5b8a145e8714245d3d225cdd`; check the latest `agent25-eleventh-root.yml` run. Once it succeeds, continue strictly in order: 3a, 3b, 3c, 3d, 3e, 4a, 4b, 4c–4g, 5a–5e. Use only successful predecessor artifacts. The earlier stage4a/4b artifacts came from the wrong branch of the dependency chain and should not be treated as the 17–30 audit.

Local `container.exec` and `python.exec` were unavailable in this invocation (ClientError), so the proof checks are being performed through the existing manual CI workflow. The exact BB(6) value and the D-machine's all-time behavior remain unresolved.
