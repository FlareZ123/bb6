# Agent32 continuation: Raw42 exact-source repair (2026-11-28)

Identity: Agent32, **normal mode RNG=6**, lease `agents/agent32/.lease.json` claimed **2026-11-28T14:34:25.574Z** (`agent32-gpt6-raw42-certificate-recovery-20261128T1435Z`). Original lease must not be refreshed. **Earliest legal release 2026-11-28T15:44:25.574Z**, only after actual-clock checkpoint, pushed memory and state, then deleting lease as the final repository mutation.

## Mathematics and accepted evidence

Raw42 retained seven-hole parent: `1RB---_1RC---_0RD---_1LD0LB_------_------`. Its twelve canonical B1 children require twelve accepted whole-child Cover theorems before the exact original `Raw42AcceptedParent.cover_global` bridge can remove its survivor from the global roster.

**8/12 accepted:** 0RB (46051022197), 0RA (45994074344), 0RE (45996645063), 1RB (45996253830), 1LA (46068374725), 1RA (46068379812), 0LA (46089669906), **1LC** ([successful run 46142055224](https://github.com/FlareZ123/bb6/actions/runs/46142055224), source-accepted `raw42-certified-1LC-split-recovery` artifact 15263231001 at weighted bound 100006). The other **4/12** remain 0LE,1LB,1LE,1RE. No Raw42 whole-parent Cover or new global roster decrement is yet justified.

## Concrete original-source 1LB rescue

Latest failed targeted recovery [46146487065](https://github.com/FlareZ123/bb6/actions/runs/46146487065) compiled `FastBiDFARows` and 12 `Raw421LBRun5137Row*` certificates to standard axioms, then failed generated wrapper at line 38 with unknown unqualified `check_of_rows`. Fixed generator `im-results/agent32-raw42/rewrite_run42_rows.py` to call `BB6.Agent32Raw42FastBiDFA.check_of_rows` explicitly, with same table/cert/row obligations, commit [1fa23c542](https://github.com/FlareZ123/bb6/commit/1fa23c54226657a3ea03b40ae12447edb8993eaa).

Dispatched [run 46155553883](https://github.com/FlareZ123/bb6/actions/runs/46155553883) with source SHA 24683e59ae88b241fbb9c7fdf907935b59010729, which includes fix. By **14:50 UTC**, prepare succeeded and subparts **1,2,3** passed source CI, subpart **0** queued. Complete 1LB source Cover is pending remaining subpart and final consumer.

## Exact-source E-branch sharding

Original full eight-shard assembly attempts: `0LE` 46142039950, `1LE` 46142043725, `1RE` 46142047495. All prepared exact generated sources and core objects but all original eight shard jobs failed/cancelled, leaving no accepted group. Failed jobs exit 143 with runner shutdown signals after kernel-checking dozens of original Run/NGram witnesses, *not* a demonstrated logical counterexample.

Created `im-results/agent32-raw42/split_all_assembly42.py`, which subdivides each original independent root group into up to four parts using generated import closure size. The script asserts **exact coverage and uniqueness** of every original root. New manual CI workflow `.github/workflows/agent32-raw42-e-split.yml` downloads the **original frozen generated source/core artifacts**, runs **32** dependency-closed Lean source subchecks with explicit axiom exclusions, authenticates exact source/object union by existing `merge_shards.py`, and only then rechecks whole-child theorem at bound 100006. No proof is claimed before final Lean acceptance. Code pushed in [cbb5b753](https://github.com/FlareZ123/bb6/commit/cbb5b7530d9baa7e716abc723ac3f190035eaf72), root loader corrected and README status reconciled in [cfe8bdc2](https://github.com/FlareZ123/bb6/commit/cfe8bdc2555a3a3f5ea80120d265216a7435f3a3).

Dispatched **pilot 0LE** source-check [run 46156341083](https://github.com/FlareZ123/bb6/actions/runs/46156341083), head caf3b22c11ed04d578ab1ccd6a93ad9778f0f87e includes root loader correction. At **14:49 UTC**, `prepare` succeeded and emitted the full 32-subshard matrix, first part `g0p2` running. Do not spin up 1LE/1RE before verifying a few 0LE parts, to avoid oversized parallel CI load and replayed failures. The named generated source modules can be split further only if isolated slow leaves exceed the 55-minute job cutoff.

Profiling original failures for possible future exact certificate compression: 0LE Run16464 234sec, Run10404 184sec, Run13265 184sec, NGram24198 86sec; 1LE NGram958 197sec, NGram29091 121sec; 1RE NGram32985 144sec. Values are bounded CI compile observations, not mathematical facts. If new single-part jobs still fail, use existing `minimize_bidfa.py`, `convert_bidfa.py`, `rewrite_run42_rows.py`, `coarsen_ngram.py` selectively on *unaccepted* source modules only; every replacement must be checked by original Lean kernel.

## Action priorities

1. Follow 1LB run 46155553883 subpart0 and parent consumer; fix the next actual source error, do not cancel successful shards. Check standard axioms, then record genuinely accepted complete child artifact.
2. Follow 0LE run 46156341083 part artifacts, diagnose first source error or oversized part, preserving successful subshards; only thereafter use identical frozen-source route for 1LE and 1RE.
3. Once all 12 children are accepted, run `agent17-raw42-parent-compose.yml` to establish whole Raw42 Cover and integrate with authenticated Canonical38 predecessor. A bound/roster decrement is not accepted before successful final source CI.
4. On/after 15:44:25.574Z (real clock) push final state/memory, delete lease **as final repo mutation**, verify remote absence; no earlier release permitted.

Local Python and shell tools returned `ClientError` before executing commands; actual source acceptance is CI only. No exact BB(6) solution, global upper bound, or publishable new theorem is claimed.
