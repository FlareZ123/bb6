# Raw112 candidate discovery

Physical partial table: `1RB---_1RC---_0RD---_1LD1RE_---1LC_------`. Six holes, 25^6 = 244140625 raw completions. Candidate discovery only, not a kernel-accepted closure.

The optimized enumerator shares known prefixes across sibling branches, and compares exact 64-bit tape windows (quick head-relative signatures can only reject cycle candidates). It uses the same first-hole branch ordering and side-cycle window as the earlier enumerator. Raw115 produced byte-identical tree and open files with both enumerators. Raw112 finished in ~8 seconds locally.

```
g++ -std=c++17 -O3 enumerate_fast.cpp -o enumerate_fast
./enumerate_fast 1RB---_1RC---_0RD---_1LD1RE_---1LC_------
```

25004 split, 446232 cycle, 115572 last-hole, 13289 open leaves. Cycle mass 216900600; halt mass 23115872; last-hole ordinary mass 2773728; open mass 1350425. Total 244140625. open.txt SHA256 61773d08354491c09508929b83a5090b564b7808e7dabf6b045d353c9ea2bf01; tree.json SHA256 93fc68780b240a41f294f311369b905a7b562f47378f9ad26e1d43e4a55c50df.

Use previous raw115 FAR and sweep generators with this open file and far-bank.txt. 12723 FAR hits; remaining 566 (mass 33950, unresolved.txt SHA256 4f8da69ac2fa75f2a59eb2dd0917e35803a7f8937f18945203f5240133ea720a); 435 single sweeps, 131 hard leaves (mass 4475, hard.txt SHA256 23805b6953da558d904471078a742f87767945ec835afd5ebe602fbb68d32f69). ngram.txt columns index-in-hard-file, width, abstract state count, left edge count, right edge count; 84 candidate certificates. late.txt identifies six actual first-hole queries (index, time, slot = 2*state+symbol), including t=91502, hence a local bound 7014 is false and the audit must use a larger bound (proposed 100000). 41 residual leaves remain. A timeout is never evidence of nonhalting. Source certificate construction is outstanding.
