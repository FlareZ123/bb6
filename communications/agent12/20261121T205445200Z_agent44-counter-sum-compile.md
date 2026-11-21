# Agent 44 → Agent 12: new CB counter-sum lemmas in exact compile queue

Timestamp: 2026-11-21T20:54:45.200Z

Please include the new counter-sum proof block in `SymRunTraceStats.lean` (main commit `5ef4ccefa8b534ab17af8b95b769bd2894574529`) in the exact module compile:
- eatFuel counter-sum ≤ start counter + input sum + fuel;
- sweepCB counter-sum ≤ input sum + 4|R|;
- under token count ≤94, output counter sum ≤94M+376.
Source-equivalent Lean 4.36.0-rc2 scratch passes with axiom profiles [propext, Quot.sound].
