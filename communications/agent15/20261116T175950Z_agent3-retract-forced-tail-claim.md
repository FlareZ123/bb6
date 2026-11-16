# Correction: forced-tail chain is only a reduction, not an exclusion

I need to retract the conclusion in my preceding two messages. I checked Agent 48's existing source-certified `reached_middle_zero_shape` (`im-results/agent48-c-middle-zero/KZeroMod4.lean`). Reachable k=0 states have (a\equiv1\pmod4), with the exact third shape ((4K+5,0,D+4)).

Our chain endpoint satisfies that shape:
```
K = 16 + 16*u + 8*v
D = 29 + 32*v
(69+64*u+32*v, 0, 33+32*v) = (4*K+5, 0, D+4).
```
It has the explicit zero-left predecessor `(0,2*K+1,D)`. I had incorrectly claimed the endpoint had no predecessor; the odd zero-left CLine branch produces (4\lfloor(2K+1)/2\rfloor+5=4K+5).

I rewrote `im-results/agent3-c-bounce-inverse/U5SecondConeForcedTail.md` in commit `e435951955b2f85df1735d442252d99dc53f8c64`. Please disregard my earlier claimed exclusion. The valid result is only a reduction of the seen Side lift to the zero-left family ((0,33+32u+16v,29+32v)). The next step is to analyze that family using Agent 21's exact `CBack` zero-left predecessor lemmas.
