# Aligned carry invariants with arbitrary entry gates

Slot codes use 0=halt, 1+4q+2write+right. Consider the partial row

    [8,a,11,?,11,13,18,15,e,24,4,12]

where a=20 or 24 and B1 is completely free. The recurrent dynamics do not query B1 or E0. More generally the two slots can be arbitrary functions on configurations; the following invariant needs neither their determinism beyond being functions nor a finite table for those two slots.

For a=20, define an E configuration with left 1^(3k) followed by zeros, scanned/right suffix in (111|110|101)*1 0^infinity. The 101 digit carries into k+1 in 3 moves; the other two digits reset k to zero with prefix 1^(3k), replacing 111 by 110 or 110 by 101, in 3k+6 moves. At the terminal 1, append a new 110 digit in 3k+8 moves. D rewind from left n ones and suffix r takes n+2 steps to E with left blank and right 1^(n+1)r.

For a=24 use F with left 1^(2k+1) followed by zeros and scanned/right suffix in (11|10|01)*0^infinity. Carry through 01 in 2 moves. Replace 11 by 10 or 10 by 01, reset k to zero and prepend 1^(2k), in 2k+6 moves. For the blank suffix, append 1010 in 2k+8 moves. These are positive exact steps to another member of the invariant. Induction on the requested finite run length proves no halt for any run length.

The following prefixes reach the invariant with k=0 starting from blank. Simulated with B1=halt, so every successful prefix avoids B1. A blank suffix denotes all zeros; all listed words have an implicit infinite zero tail.

| A1 | E0 | Live prefix steps | Suffix | Previously included? |
|---:|---:|---:|---|---|
|20|12|8|1|yes|
|20|14|7|1|yes|
|20|15|20|1111|no|
|20|18|5|1|yes|
|20|24|24|1111101|no|
|24|2|6|blank|no|
|24|4|15|1101|no|
|24|12|9|blank|yes|
|24|14|8|blank|yes|
|24|15|7|10|no|
|24|16|9|10|no|
|24|18|6|blank|yes|
|24|20|15|1101|no|
|24|23|14|1010|no|
|24|24|5|10|no|

The mathematical conclusion is 15 disjoint 25-completion nonhalting cylinders (375 tables), of which 9 cylinders/225 tables are newly identified. Under one-halt normalization this contributes nine new representatives relative to the six earlier candidates. It is not a complete first-hole cut closure.

`Box28CarryFamily.lean` expresses the general gate-independent recurrence and preserves the previous six-case API. `Box28CarryGateSource.lean` projects the exact source machine and transports the all-time invariant from a finite prefix. `Box28CarryWildcard.lean` contains fifteen explicit source theorems; `carry-wildcard-entry.json` saves the computed exact prefix data. First CI failed in source projection, not discovery; repair a5c23762 is under audit [45953999389](https://github.com/FlareZ123/bb6/actions/runs/45953999389). The new source claims remain pending until a successful named-axiom audit.
