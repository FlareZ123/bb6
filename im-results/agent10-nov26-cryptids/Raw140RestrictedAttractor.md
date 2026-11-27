# Raw140 restricted attractor: candidate extension
The pinned upstream E1 mirror sibling proof constructs a closed attractor InvM(m,z,c,k), and proves that several intermediate configurations reach it. Discovery scan of the 21 remaining one-hole candidates (not including the already-known upstream sibling id36) found 19 entries into those intermediate invariant families, with exact primitive step counts below. These are computational hypotheses until the entry and restricted invariant proofs pass.

```
28 158926095 convSimple 5 2741 455 4
31 32670175 convSimple 3 1286 183 4
35 30602463 convSimple 5 1301 155 4
37 32014873 convSimple 1 1321 163 4
39 31019601 convSimple 1 1213 201 4
40 32014893 convSimple 1 1321 163 4
41 102682281 convSimple 5 2349 298 4
42 35739853 convSimple 3 1305 216 4
43 17217036 eClean 270 1 140 1516
44 32014863 convSimple 1 1321 163 4
45 48256951 convSimple 4 1589 207 4
46 32670185 convSimple 3 1286 183 4
74 17217048 eClean 270 1 140 1516
77 31019501 convSimple 1 1213 201 4
81 166291157 convSimple 2 2804 466 4
83 32014883 convSimple 1 1321 163 4
85 36728347 convSimple 2 1416 174 4
86 158925615 convSimple 5 2741 455 4
88 167841615 convSimple 3 2817 468 4
```

73 and 80 did not match these invariants by 200 million primitive steps. The proposed proof explicitly changes the mirror table to leave D1/F0/F1 undefined, excludes macros reading D1, and recompiles the retained invariant proof in a new module; original upstream source is unmodified. This is necessary to obtain an extension-safe theorem rather than incorrectly transport a full-machine proof. Entry proofs need variant-sensitive exact evaluation, not simply the common restricted evaluator: the last use of an unfixed row occurs up to tens of millions of steps from blank.

No additional accepted Cover claimed here yet. Source license and copyright are preserved in generated module. Upstream commit d1d231afe3a5f6310ac9f956d5687b5a45d7a13d, module M_1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LAHHH.


## Two remaining siblings (2026-11-27)
The previous two unresolved local IDs 73/80 exhibit a separate candidate doubling recurrence; see [Raw140DoubleGrowth.md](Raw140DoubleGrowth.md). This is finite evidence, not an attractor or nonhalting proof.
