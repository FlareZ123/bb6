# Raw124 F1=0LF / F0=0RB: complete weighted child certificate

**Status:** original-source GitHub Actions CI accepted (run `45829435208`), no remaining leaves. This is an intermediate child cover, not the full Raw124 parent.

```lean
BB6.Agent4Raw124ZeroLF0RB.bound_all :
  ∀ m, compatible BB6.Agent4Raw124ZeroLF0RB.pChild m → WeightedBound 174 m
```

Literal partial table: `1RB---_1RC---_0RD---_1LD1RE_---1LF_0RB0LF`.
This is the four-hole child, representing 25^4 = 390625 tables. Exact untrusted discovery uses cap 3000 and lookback 32. Maximum query time is 168; bound 174 allows the weighted initial delay and halt step. The original checked weighted TNF theorem handles all refinements and delays.

| Kind | Count | Completion mass |
|---|---:|---:|
| Split nodes | 171 | included in terminal bounded mass |
| Cycle leaves | 2970 | 315450 |
| Last leaves | 777 | 48300 (including split halt choices) |
| FAR-proved leaves | 182 | |
| Two-sided run-language leaves | 5 | |
| Open-leaf total before proofs | 187 | 26875 |
| Unresolved after certificates | 0 | 0 |

The five hard leaves use retained-run finite abstractions: lengths below threshold remain exact; above threshold are reduced modulo the specified period. The Lean checker verifies inverse-pop closure, blank reachability, and that no reachable pair of stack classes can query a missing transition. Thus each certified partial machine is nonhalting under every completion, not merely simulated for a bounded time.

| Open-list index | (retained runs, threshold, period) | reachable pairs |
|---:|---|---:|
| 9 | (5,3,4) | 781 |
| 170 | (5,3,4) | 707 |
| 183 | (3,1,5) | 623 |
| 184 | (3,1,5) | 361 |
| 185 | (3,1,5) | 425 |

## Reproduction

Run `python im-results/agent4-raw124-0lf/generate_0rb.py OUTPUT_DIRECTORY` from the repository checkout; the generator uses the existing Raw124 fast partition and Agent11 FAR search through six DFA states. It asserts the ordered partition and open-list SHA256 digests and complete disjoint proof assignment. Compile the generated modules in import order with Lean 4.36.0-rc2 and the existing `Raw124FastAudit` and `TwoSidedAutomata` dependency closure. The proof generator emits `by decide`, never `native_decide`. Local compilation concatenated small independent subtrees into their top-level child modules to reduce process overhead.

Local verification finished 2026-11-26 11:18 UTC, using the checked Raw58 artifact 15090715339 (run 45762057732) for the original dependency closure and the exact tracked Raw124FastAudit source (Git blob 6a6086dd9e41d924606a7ce9b1784d0486f04220) compiled against that closure. Lean binary SHA256 db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00 matches the artifact compiler. A fresh GitHub Actions source-only build has not been run.

Actual final Lean output:

```text
'BB6.Agent4Raw124ZeroLF0RB.checkRoot' depends on axioms: [propext, Classical.choice, Quot.sound]
'BB6.Agent4Raw124ZeroLF0RB.bound_all' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Generated final source SHA256: 4e13c72591e9a38fe28ada5a44812d5dabff1231e3b3186096aa190b95d2a73e. No sorryAx. No new global roster change.


## Original-source CI acceptance (2026-11-26 13:32 UTC)

The complete generated theorem was rebuilt from the tracked generator and original source dependencies in [run 45829435208](https://github.com/FlareZ123/bb6/actions/runs/45829435208), source commit `4f7e22bbbec59ed9c3d23908b5262caec40f239b`. The workflow pinned `Raw124FastAudit` blob `6a6086dd9e41d924606a7ce9b1784d0486f04220` and `TwoSidedAutomata` blob `c04bf81e19d55b3d028c714e628246a4b917f03c`, regenerated the exact partition/witness assignment, compiled 443 project modules, and passed the axiom audit for both `checkRoot` and `bound_all`.

- Artifact: `raw124-0lf-0rb-source-accepted`, ID `15121597506`, SHA-256 `2f9f9cabea804463972455c1e4bb2d6c74cea9014a3ec6808ea93341fbc1e214`.
- Exported theorem: `BB6.Agent4Raw124ZeroLF0RB.bound_all`.
- Weighted bound: **174** over all 390,625 completions.
- Exact axiom profile for `checkRoot` and `bound_all`: `[propext, Classical.choice, Quot.sound]`; the automated axiom audit passed.
- The artifact includes the generated proof sources, source-closure manifest, and audit log.

This is the F1=0LF/F0=0RB child only. It does not close the entire F1=0LF branch or Raw124 parent, and it is not a Canonical64 roster subtraction.
