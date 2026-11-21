# Lean 4.36.0-rc2 source-acceptance preflight

**Status: the complete five-family theorem is not yet compiled or accepted.** The frozen 93-progression candidate remains in `im-results/`. The integrated theorem `SheepPower1458.noEvenReachFiveFamilies` is present in `SheepPower1458TreeProof.lean`, but no successful compiler run of its complete current-main dependency closure is available.

## What has been checked, and what has not

- The source-independent `SheepPower1458AffineBounds.lean` dependency closure was locally compiled in an earlier 21 November rc2 run (see `communications/agent14/20261121T084000Z_agent17-affine-closure-compile.md`). The recorded profiles for `no_generic_high_affine` and `no_special_affine` contain only standard Lean axioms and no `sorryAx`.
- Agent 14's 08:00Z parity handoff identified the missing source-even premise in the outer `TreeProof` closure. Agent 14 separately compiled only the standalone pure-Std `genericChildValue` algebra helper. The shared evidence does **not** record a successful compile of the parity-aware `SourceIntegration` or integrated `TreeProof` closure.
- The shared `SheepPower1458SourceIntegration.lean` now requires `hx : x % 2 = 0` in `affine_edge_inverse_cases`. Its reverse-basin closure and `SheepPower1458TreeProof.lean` carry this premise; `EvenReach.cons` propagates evenness with `even_edge_even`. This repairs the genuine counterexample `EvenEdge 5 10` to the former parity-free premise.
- Agent 40's independent exact-integer audit found the frozen low-a classifier has 555 cases per family aggregate: 15 listed intermediate edges plus 540 non-hit rows, with no missing/duplicate row keys. It also checked all 24 stored affine edges and the global exceptional-source coefficient bounds. This is static arithmetic review, not Lean compilation.
- A focused source review then found a definite direction error in the root cutoff subproof: `hnotHigh` is a negated lower-threshold proposition, but the old script attempted to prove the forbidden lower bounds directly. Commit `f171ed94040312e2bfa411125b4b88c0da3adf6e` now derives `¬ 2 ≤ a` for `h=0` and `¬ (2*h+3) ≤ a` for `h>0`, then closes the desired upper bounds. This removes an obvious proof-script blocker but remains uncompiled.
- A static token scan of the 12 current 1458 Lean modules found no occurrences of `sorry`, `admit`, `axiom`, `native_decide`, or `unsafe`. This is only source inspection; it does not establish compilation or the transitive axiom profile.
- The new `SheepPower1458LowRowTable.lean`, `SheepPower1458RootEdgeTable.lean`, and integrated `SheepPower1458TreeProof.lean` have no recorded successful compile in their current shared form. The theorem-level transitive axiom profile for `noEvenReachFiveFamilies` is therefore unknown.

## Current local-runtime blocker

In this invocation, the prescribed local bootstrap command (concatenate the supplied split ZIP, unzip the outer archive, extract its inner `.tar.zst`, then run `lean --version`) failed at the tool boundary: `container.exec` returned `ClientError` before executing the shell command. A trivial Python runtime check also returned `ClientError`. No archive extraction occurred and no Lean process or compiler diagnostic was obtained. This reproduces the environment blocker already reported by Agents 1 and 40; it is not evidence of a Lean source failure.

**CI was not dispatched.** Repository guidance requires a successful local rc2 preflight before using the existing manual source workflow; CI must not substitute for that preflight.

## Exact acceptance path

Reuse `.github/workflows/agent14-sheep-power1458-tree-preflight.yml`. It reconstructs the pinned Agent16 Sheep source archive, compiles the original `SheepEven` / `EvenEdge` / `EvenReach` source modules and the inverse/source algebra dependencies, then compiles the 1458 modules in dependency order through `SheepPower1458TreeProof.lean`. Do not create another workflow, add residue classes, or repeat the already-completed period/row audits.

The outstanding acceptance action is one local rc2 compile of that exact current-main closure, followed by inspection of `#print axioms SheepPower1458.noEvenReachFiveFamilies`. The required result is either a successful full compile and an axiom profile without `sorryAx`/unapproved oracles, or the first concrete compiler diagnostic. Until then, the 93-family statement remains an unaccepted original-source proof draft, not a Sheep or BB(6) decision.
