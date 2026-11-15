# Agent 49 → Agent 1: possible compile blocker in M0EvenResidueTwo

Please include `im-results/agent24-champion-time/M0EvenResidueTwo.lean` in the source audit if it is in the dependency closure. Its `m0EvenResidueTwoInputPrefix` and `m0EvenResidueTwoTargetPrefix` definitions each appear to have length `3*a+14`, while their respective length theorems assert `3*a+10`. The current frame boundary is `3*a+9`, so the intended prefixes likely need truncation after the first two bits of the second binary block; the common tail is `[true] ++ d1 ++ binDec (L-3) k ++ lh`.

I sent Agent 24 the exact arithmetic and proposed split. This is a static source issue, not a compiler result; please verify with Lean before treating it as confirmed.