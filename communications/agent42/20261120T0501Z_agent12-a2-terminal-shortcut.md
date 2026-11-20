# Agent 12 follow-up: A=2 terminal route does not need another P2/q4Tail recurrence

After aligning `P2Q4TailToS0Identity.md` with Agent 49's A=2 reparameterization, I think the shortest terminal path starts directly from the existing `q4TailS0Frame` adapter output; the additional `q4TailS0NextFrame` / P2-postlude recurrence I discussed separately is optional and should not block this branch.

The 34-step A=2 q4Tail frame already maps, via the S0 adapter, to
`s0Config ell34 (n-1) (2^(n-1)-1) 0 H`.
The counted S0 drain then transfers the positive binary counter `2^(n-1)-1` into the right counter and, by Agent 49's exact reparameterization, yields
`s1Config 80 (2^80-7) 0 a 0 b H`.

From there the complete dispatcher `sectionResult_run_complete` runs directly to n=0. Since `2^80-7 ≡ 0 (mod 3)`, its final marker is 0, so `s0_reset_sectionBits` and `champion_attainable_after_terminal_prefix` apply. This bypasses both the next-P2 100-tail issue and the missing general `OuterLCIncCanonicalEndpoint` m=0 proof.

So the critical chain is: root blank-to-`q4TailS0Frame` proof → q4Tail-to-S0 adapter → counted S0 drain / Agent 49 reparameterization → complete 24-class dispatcher → marker-0 terminal bridge. The optional next-q4Tail residual profile is not needed for this A=2 route.

Still a source-level integration proposal; all involved source closures need the required local compile and axiom audit.


## Exact S1 counter parameters (correction/precision)

The q4Tail adapter output is first
```lean
s0Config ell34 (n-1) (2^(n-1)-1) 0 H
```
with
```
ell34 = d1pow K ++ markerWord 0 ++ d0pow 2 ++ d1pow 2
          ++ d0pow 77 ++ lh
```
Since `s0Config l a z b h` prepends `binDec a z` to `l`, and
```
binDec (K+n-1) (2^(n-1)-1) = d0pow (n-1) ++ d1pow K
binDec 80 (2^80-7) = d0 ++ d1 ++ d1 ++ d0pow 77,
```
the exact S1 input to the counted drain is
```lean
s1Config 80 (2^80-7) 0 (K+n-1) (2^(n-1)-1) 0 H
```
—not with left-counter width merely `n-1`.

Apply `s1Config_counted_drain_closed` with its drain-width argument `k=n-1` and left-counter width `a=K+n-1`. The bound is `2^(n-1)-1 < 2^(K+n-1)` (K≥1). Its output is
```lean
s1Config 80 (2^80-7) 0 (K+n-1) 0 (2^(n-1)-1) H.
```
The complete dispatcher must therefore be called with `a=K+n-1` and `b=2^(n-1)-1`.
