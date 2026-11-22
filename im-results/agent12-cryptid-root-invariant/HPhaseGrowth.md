> **WITHDRAWN / NOT SOURCE-VALID (2026-11-22):** This projected corridor/H-phase analysis was built on the transition simulator whose CR-left-prefix 1,0 / 1,1 / 1,>=2 clauses and empty-list bump do not match the pinned #85 source. Do not use its macro counts or root-connectivity claims until the projected rules are corrected and independently audited. See [the critical CR-branch correction](../../communications/broadcast/20261122T0813Z_agent12-critical-CR-branch-withdrawal.md).

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

The 157-successor H(7)-to-C1 entry re-matches under the source-faithful b==0 replay, with zero token-normalizer calls and a branch-counted cost of 526 raw TM steps. This is a standalone projected transition, not a Lean proof. The old root-to-H(7) connection remains withdrawn. A direct source-transcribed check of the root-reachable instance H(1939) is also negative: the blank-root trace reaches H(1939) at macro 1,113,215 (9,731 successors after D_484(1)), but 157 successors from that state end in EL with left-list length 3,857 and right-list length 39, not in C1. Thus the H(7) entry cannot simply be generalized to the root's H(1939) state. Do not infer blank-root reachability from the H(7) entry or 76-step identity alone. If the arbitrary-suffix macro is formalized, it gives an infinite orbit of the projected stack system from any valid seed in this family; an original-TM nonhalting result additionally requires a source-checked entry and lift.

## Raw-step bookkeeping

The H-phase 76-successor growth macro totals 254 raw TM steps. The H(7)-to-C1 entry totals 526 raw TM steps across 157 outer successors. Both totals are branch-counted V8 bookkeeping, not Lean theorems. The immediate proof target is a suffix-parametric execution theorem against the pinned #85 source, with explicit endpoint encodings and a transitive axiom audit.

See [ModeDRBranchAudit.md](./ModeDRBranchAudit.md) for the DL/DR source split and [RootCountdownGrowth.md](./RootCountdownGrowth.md) for the separate root-connected DR/G/B growth candidate.
