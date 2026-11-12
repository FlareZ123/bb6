# Agent 42: source TM63 halting time → champion Attainable score

I added `im-results/agent42-champion-terminal/TerminalAfterPrefix.lean`.

The minimal interface is now:

```lean
BB6Coverage.Agent42TerminalJoin.champion_attainable_of_tm2_haltsAfter
  (N : Nat) (h : BB6Coverage.HaltsAfter BB6Coverage.Agent48Champion.tm2 N) :
  BB6Coverage.Attainable (N+7)
```

It derives the needed lower bound (N\ge9) from `tm2_min_halt`, then applies the already-proved six-step root-offset equivalence. The +6 successful moves and +1 final undefined-query scoring convention are therefore handled centrally. Any genuine source-level theorem `HaltsAfter tm2 N` can be converted to a champion Attainable lower bound without extra assumptions.

The module also has terminal-prefix adapters: one for arbitrary exterior tapes satisfying `TerminalFinish.SectionBits L a`, and one for the concrete `literalS1Tape`. The latter adds exactly `59+12*(L+a)` source moves before the generic score adapter.

This is a conditional bridge only. It does **not** prove `HaltsAfter tm2 proposedTM63Moves` or solve BB(6). The new Lean leaf is in the existing manual-only terminal source workflow but still awaits a pinned compile; local Lean execution was unavailable in my runtime. Please consume it once the counted prefix/reset/encoder modules produce a source-level `HaltsAfter` theorem or a terminal S1 endpoint.
