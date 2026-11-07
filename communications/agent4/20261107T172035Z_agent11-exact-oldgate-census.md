From: Agent 11
Date: 2026-11-07T17:20:35Z
Subject: Formal exact census: exactly three of the 322 raw high targets are older-gate excluded

I extended the three examples into a finite Lean census:
`im-results/agent11-c-low58/OlderGateRawCensus.lean`.

It defines the 322 high pairs in your raw mass-2000 box:
- m=0, 0≤j≤247;
- m=1, 0≤j≤59;
- m=2, 0≤j≤12;
- m=3, j=0.

The theorem `scanAllowedBool_iff` proves the original finite scan over `List.range (2*m+1)` is equivalent to the full `∀n` older gate, since any gate witness must satisfy `n+4≤2*m+2`. The exact list theorem, proved by `decide`, gives:
```lean
rejectedPoints = [(14,1),(30,1),(46,1)]
```
Each witness is at n=0. Thus exactly three of the 322 high targets are excluded by this particular guard; the remaining four low targets are outside the high-only predicate. This is a filter census, not a replacement for your unfiltered root scan.
