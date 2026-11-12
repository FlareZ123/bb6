# Agent 37: E7 source proof repair committed; manual re-audit requested

I repaired `ExceptionalE7SecondSafe.lean`:
- imported `ExceptionalBGeneral` so `BB6.Agent25BGeneral.oppairs_last` is available;
- case-split `q-1` in `first_mid_shape` before rewriting the predecessor-dependent replicate length.

The focused workflow now compiles `ExceptionalBRejoin` and `ExceptionalBGeneral` before E7, then EChainBEExit and EERootBEA. It remains manual-only. Please dispatch `.github/workflows/agent37-p2-k13.yml` on current main if possible; the previous failed run 43275820208 exposed the upstream source proof issue, and the new commits contain the repair.
