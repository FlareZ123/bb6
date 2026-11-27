# Raw40 / A1=0LA / C1=0RD / leaf154: exact two-pump crossing recurrence

**Mathematical nonhalting certificate with executable finite premises; not yet Lean accepted.**

Literal table `1RB0LA_1RC1RE_0RD0RD_1LD1LA_---0RF_0RC0RA`. The only hole is E0.

## Result

Write [g,b] for the bit word 0^g 1^b. Concatenation is in increasing tape coordinate (right of the head).

* P = [27,5][3,10][23,5].
* A = [3,5], B = [7,5], S = [7,10].
* M is the concatenation of [g,5] over the list of gaps
  7,7,15,7,27,3,7,7,11,7,3,11,7,7,7,3,11,7,3,7,11,11,3.

For n>=0 and integer h, define X(n,h) as state A scanning blank at h, every cell at or left of h blank, and right word

`P A^(14+n) M B^(10+2n) S`,

with all cells further right blank.

The blank execution reaches X(0,-480) after exactly **132476** assigned transitions. For every n>=0 and h, the assigned transitions take

**X(n,h) -> X(n+1,h-24) in exactly 12262+520n transitions.**

Thus every completion of E0 is nonhalting.

## Finite certificate

The [standalone checker](check_leaf154.js) replays the blank entry and the 12262-transition base epoch, checking both entire endpoint tapes, their state and head, and the absence of unassigned moves. It passed in the JS runtime.

Translate the entry head to 0. The base epoch ends at -24. On the edge between cells x and x+1 record chronological pairs (crossing direction, next state). State numbers A=0,...,F=5. The two disjoint cut intervals have identical crossing sequences at their respective endpoints:

| Cut edges (a,b) | Crossing list at both edges | Departures from cells (a,b] |
|---|---|---:|
| 73,81 | R3 L3 R4 L0 R3 L3 R4 L0 | 104 |
| 489,513 | R3 L3 R4 L3 R4 L0 R3 L3 R4 L3 R4 L0 R3 L3 R4 L0 | 416 |

Both intervals are strictly to the right of both endpoint heads. The right word lengths are 626 and 658. The start's A-power occupies offsets [73,185), the finish's [73,193). The start's B-power occupies [489,609), the finish's [497,641). Relative to the finish head the cut offsets increase by 24, hence the two intervals lie within their corresponding periodic regions at both ends:

* first: [73,81) and [97,105), one whole period of A;
* second: [489,513) and [513,537), two whole periods of B.

The offset convention is that cells (a,b] correspond to the zero-based substring [a,b) to the right of head 0.

## Unbounded proof

Use the [crossing-sequence splicing lemma](../agent42-raw40-crossing-splice/README.md#splicing-lemma-finite-computation-arbitrary-repetitions): for disjoint intervals with equal chronological boundary crossings, neither endpoint head inside the intervals, duplicating each interval's local cell transcripts any number of times gives a valid computation on the corresponding expanded endpoint tapes. The total added departures equal the sum of copied interval departure counts.

For completeness the word identity is elementary, not extrapolation. If a substring of p^k begins at any phase of p, has length d*|p|, and lies wholly in p^k, replacing that substring by n+1 copies gives p^(k+dn), as each copied character is at the same phase modulo |p| and the rest of the word is displaced by a multiple of |p|. This holds even when the start and finish cut phases differ.

The first interval inserts n extra A blocks at each endpoint. The second inserts 2n extra B blocks at each endpoint. Neither changes P,M,S or either head. Starting from the actual base epoch X(0,0) -> X(1,-24), splicing gives X(n,0) -> X(n+1,-24), at cost 12262+(104+416)n. Translate to arbitrary h and iterate from the authentic blank entry. Every spliced transcript is transition-valid and assigned. This proves arbitrarily long live prefixes, independent of how E0 is completed.

## Discovery and integration

The decisive step was to inspect every sixth left-frontier return instead of generic finite-state abstractions. The large late trajectory revealed a fixed middle word and two growing periods; testing exact equal boundary crossing lists on a full 24-frontier epoch supplied the unbounded proof. The earlier attempts did not close this leaf. No claim is made that merely observing the two growth rates proves them.

Together with the separate [leaf66 nested run-drain proof](A0LA1LC-leaf66-normalized-drain.md), this closes both outstanding mathematical residuals in Agent42's targeted 30-leaf snapshot. Formal source certification, complete child audits and global roster integration remain separate obligations. This certificate can use Agent42's developing crossing-source consumer; the finite data here do not rely on its acceptance.
