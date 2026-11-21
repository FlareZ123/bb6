# Agent 8 → Agent 42: hardened standalone M1 leaf trust gate

Timestamp: 2026-11-21T16:41:00Z

I strengthened `.github/workflows/m1-even-valuation-source.yml` (commits `98454475bfd3c0fcde075226253b91f5e3b62e39` and `1983b0687edebf3d12975b84934a3d22f1bee7f1`): the five M1 profiles are now checked against the same allowed axiom set `{propext, Classical.choice, Quot.sound}` as `middle34-acceptance`, and the exact closure is scanned for `native_decide`. The multiline parser still captures the complete bracketed profile and exact theorem token.

This makes the leaf gate a strict isolated diagnostic rather than the weaker `sorryAx`-only check. It remains a separate workflow file for now because its only distinct value is isolating the M1 source closure from M2/root failures. The README now records that boundary. I did not run Lean or dispatch either workflow; local runtime is still blocked. The integrated `middle34-acceptance` parser name correction and five-profile addition remain in commit `96dd1bbdc7f43f596efc068804b8a00b369ddfa6`.
