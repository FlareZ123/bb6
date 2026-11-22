# H-phase CR growth identity

**Status: source-transcribed macro candidate; not a Lean theorem.** The previous withdrawal of this identity was based on the erroneous `mode_DR` condition `b <= 1`. The pinned source tokenizes only right-head 0 in `mode_DR`; positive right heads, including 1, take the ordinary branch. With that source-correct branch restored, the 76-successor H-phase CR test passes and makes zero token-normalizer calls. Its H(7) entry and root reachability remain separate obligations.

Set

```text
P = [0,0,1,0,19]
B = [0,0,0,2,0,0,0,2,0,0,0,16]
U = [0,0,0,12,0,0,0,12,0,0,0,12,0,0,0,2,0,0,0,0]
```

The candidate tail-parametric identity is

```text
S^76(CR(L=[1,0], R=P ++ B ++ T))
  = CR(L=[1,0], R=P ++ B ++ B ++ T)
```

for every finite suffix `T`. The current checked-in regression replays the fixed suffix `U` and verifies the exact endpoint with no token calls. Earlier V8 work recorded additional finite numeric suffixes and an opaque sentinel, but those tests should be rerun against the current harness before being treated as current reproducibility evidence. The source-correct branch is `b === 0` in DR.

The 157-successor H(7)-to-CR entry and the claimed root-to-H(7) connection have not been revalidated here. Do not infer blank-root reachability from the 76-step identity alone. If the arbitrary-suffix macro is formalized, it gives an infinite orbit of the projected stack system from any valid seed in this family; an original-TM nonhalting result additionally requires a source-checked entry and lift.

## Raw-step bookkeeping

The earlier branch table totals 254 raw TM steps for 76 outer stack successors on this H-phase path. This is bookkeeping for the proposed macro, not a Lean theorem. The immediate proof target is a suffix-parametric execution theorem against the pinned #85 source, with explicit endpoint encodings and a transitive axiom audit.

See [ModeDRBranchAudit.md](./ModeDRBranchAudit.md) for the DL/DR source split and [RootCountdownGrowth.md](./RootCountdownGrowth.md) for the separate root-connected DR/G/B growth candidate.
