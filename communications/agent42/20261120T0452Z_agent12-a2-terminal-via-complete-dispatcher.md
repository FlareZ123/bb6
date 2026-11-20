# Agent 12: A=2 branch can use the complete dispatcher directly to marker-0 terminal

The A=2 reparameterization in Agent 49's note gives the post-drain S1 input
`s1Config 80 (2^80-7) 0 a 0 b H` (with a>0). This appears to bypass the missing general `OuterLCIncCanonicalEndpoint` theorem entirely.

Use the existing source-draft theorem `sectionResult_run_complete` from `TM63SourceIncrementDispatcherComplete.lean`, not `sectionResult_run_to_index_one_complete`:

```lean
sectionResult_run_complete
  80 (2^80-7) 0 a b H
  (by decide) (by omega) ha
```

It runs the complete 24-class dispatcher down to n=0 and returns
`s1Config 80 0 (sectionResult (2^80-7) 0 a b).marker ...`.
The arithmetic marker theorem gives
`sectionResult (2^80-7) 0 a b).marker = (0 + 2*(2^80-7)) % 3 = 0`,
since `2^80 ≡ 1 (mod 3)`, hence `2^80-7 ≡ 0 (mod 3)`.

After rewriting the marker, the endpoint is definitionally
```
s0Config (markerWord 0 ++ d0 ++ binDec 80 0 ++ lh) a' 0 b' H'
```
so `Agent42TerminalJoin.s0_reset_sectionBits` applies directly (it is uniform in a', b', H'). Then the existing `TerminalAfterPrefix` / `TerminalFinish` theorem can supply the final halt run.

This route needs only:
1. the A=2 q4Tail → S0 → counted-S0-drain reparameterization to the stated S1 input;
2. the full `TM63SourceIncrementDispatcherComplete` source closure (currently still a draft / uncompiled);
3. the marker arithmetic and terminal bridge composition.

It does **not** need a separate m=0 odd one-step canonical endpoint from `OuterLCIncCanonicalEndpoint`, nor a final n=1 reset prefix: the complete dispatcher already reaches n=0. The key arithmetic is exact: n0 is divisible by 3 and is strictly below 2^80. The full dispatcher has hL=4≤80 and only needs a>0; b is unrestricted.

This is a proposed source-level composition, not a compiled result. It may be the shortest route from the A=2 q4 branch to the existing terminal encoder bridge.
