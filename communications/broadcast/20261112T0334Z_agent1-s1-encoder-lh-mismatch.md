# Agent 1: S1 encoder fixed-left-prefix mismatch

I found a concrete source-encoding discrepancy that should be corrected before the new S1 encoder is used in counted champion proofs.

## Exact discrepancy

The pinned BusyCoq source `verify/SOBCv5.v`, inside `Module TM63`, defines

```coq
Notation lh := (0inf <* <[1;1;1;0;1;1]).
Definition S1 len0 a0 m len1 a1 b :=
  S0 (LC lh len0 a0 <* d0 <* m) len1 a1 b.
```

The physical left-to-right fixed prefix is therefore `111011`. The existing independent raw-step harness `im-results/agent24-champion-time/verify_counted_macros.py`, function `s1`, encodes the complete physical left word as

```python
left = "111011" + lc(length, n) + "100" + markerword + lc(a, a1)
```

By contrast, `im-results/agent8-s1-encoder/S1Encoder.lean` currently defines

```lean
def lh : List Bool := [true,true]
```

and consequently `s1PhysicalLeft_m0_zero` yields only `11 ++ 111^L ++ 100 ++ 10 ++ 111^a`, omitting four source cells.

## Reproduction

I independently simulated the literal twelve-entry `tm2` table from the blank A-root for exactly 27,959 primitive transitions. The resulting full sparse tape, head and state match the harness's `s1(3,7,2,6,0,63)` exactly: 225 marked cells on each side of the comparison and zero differing coordinates. In particular, the physical prefix is `111011`, not `11`.

The corrected head-facing word should be

```lean
def lh : List Bool := [true,true,false,true,true,true]
```

(the reverse of physical `111011`).

Please update the encoder's downstream equalities and run its original-source CI before using it as the canonical S1 source interface. The independent finite-tape sweep lemmas do not depend on this encoding and are not implicated; only claims whose source S1 configuration is built through the current encoder need correction.
