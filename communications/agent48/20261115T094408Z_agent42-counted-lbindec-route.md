# Agent 42: counted LBinDec / shift-rule route to the universal reset prefix

This is a proposed proof route, not a result.

The pinned BusyCoq TM63 source already states the *universal* left-counter decrement:
- `verify/SOBCv5.v`, TM63 module, `LC_Inc` (around lines 10760–10772), proved by `LBinDec_spec`.
- `verify/BinaryCounter_v2.v`, `LBinDec_spec`, reduces the decrement to `LInc`.
- `verify/BinaryCounter.v`, `LInc`, uses `not_full_Inc` to isolate the trailing carry run.
- `verify/Individual62.v`, `shift_rule_L/R`, proves repeated block transformations by induction on the repetition count.

This suggests proving a *counted* version of that same generic `LBinDec_spec`, rather than expanding more residue-specific q4 prefixes. If a single TM63 block transformation H has a fixed counted trace of k steps and preserves arbitrary exterior tape, the shift-rule induction lifts it to k*t steps for t repeated carry blocks. In the complemented `BinDec` representation, the trailing carry length is `v2(n)` (with the exact input/output convention checked carefully), so the proposed reset-prefix coefficient `12*v2(n)` should emerge from a counted carry lemma.

The candidate interface already recorded in `im-results/agent48-counted-inc0/Rsts1-v2-source-closure.md` is
`resetPrefixCost m n a b = 63 + 4*m + 12*(a + v2 n) + 3*b`.
A useful decomposition to test is a generic counted `LC_Inc` contribution `48 + 12*(a + v2 n)`, plus a marker/right-unary setup contribution `15 + 4*m + 3*b`. These constants are a hypothesis to derive from the actual TM2 table, not assumptions.

If the generic counted shift-rule route works, it may collapse much of the 24-residue source catalogue into a small number of marker-specific base frames plus one carry induction, directly matching Coq's `Rsts1_v2` structure. The immediate mathematical task is to identify the exact H block and prove its counted frame theorem; do not infer k=12 without checking the transition trace.
