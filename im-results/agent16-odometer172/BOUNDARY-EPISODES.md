# Exceptional boundary episodes: limits of local safety

The positive-tail epoch lemma does not extend to all safe all-H preparations. The obstruction is not just the choice of signed potential.

## Exact counterexample to a local birth-guard induction

Start with phases HHHHH, boundary empty, and gap vector (0,469,1216,19198,10936,218). All four internal charges are 1, the first following gap exceeds 3^5, and the trailing gap is positive. Nevertheless the next birth violates the signed birth guard. With zero-based particle indices, the exact event trace is:

| Event | Pre-event time | Pre-event phases | Pre-event gaps | Boundary | Action |
|---|---:|---|---|---|---|
| 1 | 1409 | LL DLH (i.e. L,L,D,L,H) | 1409,0,1060,19146,10919,212 | empty | pair at 0 |
| 2 | 7157 | HHL | 8218,17230,10280,0 | empty | drain at 2 |
| 3 | 7166 | HH | 8227,17227,10279 | 0 | positive-tail birth |

The post-birth state at time 7167 is HHH, boundary 1, gaps (0,8228,17227,10278). Its new internal charge is 8228 mod 3 = 2. The signed potential P0 of the suffix [(H,17227),(H,10278)] is 51687, since its inner R1 vanishes. Thus 8228 < 51687, and the new gap is not protected. This refutes the proposed *unconditional* extension, not the actual blank trajectory BirthGuard. The prepared starting state is not claimed reachable.

A second prepared state HH, boundary 1, gaps (0,52,0), with charge 1 and first gap exceeding 3^(2-1), hits an unsupported L,H interaction at the 532nd event, pre-time 152091176, particle index 8, boundary 0. The phase list is HHHHHHHHLHLHL; gaps are (5558895,2930140,30420712,29514985,5009782,1559233,471421,536812,23588,0,17030,3230,32,35). This is a genuine failure of the projected safe-transition condition, not a proof of eventual halting from this preparation. In the word rewrite the next digit 3 is incremented to 4, but whether it is subsequently scanned requires separate analysis.

Both examples can be reproduced using the existing exact event accelerator; see boundary_counterexamples.py.

## A sufficient preceding-birth inequality

Consider a post-birth state with leading gap 0, all phases H, first following gap G, and nonempty suffix Y. While there are no births, write N for the leading gap and P0 for the signed potential of the whole cell list. Each projected carry on a nonempty list increases N by 1+e and lowers P0 by at least 1-e. Thus N-P0 increases by at least 2 until the list is empty. Initially P0=3G+3+P1(Y).

If the first particle is ever removed by a pair deletion, at least 3G+3 high-level transitions must have elapsed: from H, two transitions reach L; each of the G intervening L-to-H cycles requires three transitions, and the deletion takes one further transition. A deeper deletion can only increase the first following gap, delaying this event. Therefore the sufficient initial inequality P1(Y) <= 3G+3 gives N >= P0 at that deletion and thereafter, until another birth. Any following nonempty birth suffix has P0 no greater than the current P0, so the new gap N+1 is protected. If no first-particle deletion occurs, its phase cycles modulo 3 and N increases by 1 at each carry, giving charge 1 at the next birth; if the first particle drains alone, there is no new internal gap at an empty birth.

This inequality is sufficient, not necessary and not a trajectory invariant. The actual trajectory already violates it at numerous good births. In a diagnostic scan, thin-tail cases at events 458, 5226, 124062 and 124064 failed it; event 124075 nonetheless produced a protected exceptional gap. A solution must exploit actual reachable history or a sharper conditional bound.

## Empty-boundary episode decomposition

With boundary empty and at least one particle, no birth occurs and all-H wraps preserve the boundary. Every pair or drain strictly reduces the number of particles. The exact next deadline can therefore jump across wraps; a whole empty-boundary episode has at most the initial particle count many such reduction events before either reaching boundary 0 or eliminating every particle. The latter state is an all-2 word and grows by prepending 2 forever (Word.scan_end). This is a finite symbolic reduction for an arbitrary episode, not a bound on the number of episodes along the blank trajectory.

## Status

The conditional source bridge is being audited independently. No unconditional decision of #172 or global BB(6) bound follows from these observations.
