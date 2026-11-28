# Event-driven evaluator of F421 positional lifetimes

**Status:** independently tested exact-arithmetic numerical evaluation; mathematical source bridge is separately established in Lean. This file is computational infrastructure, **not** a nonhalting certificate or an unconditional BB(6) result.

## Event-driven representation

The far-to-near positive lifetime recurrence is source-defined and formally proved in [F421SecondaryLifetimes.lean](F421SecondaryLifetimes.lean):

- A positive lifetime \(l=1\) is deleted, incrementing the running number \(d\) of deletions.
- Any survivor \(l>1\) becomes \((l-1)2^d\).
- Finally append \(2^{D+1}\), where \(D\) is the total number of deletions.

The naive implementation takes \(O(km)\) arithmetic operations over \(k\) cycles and a growing length \(m\). [fast_lifetime.cpp](fast_lifetime.cpp) stores the lifetime list in an implicit randomized treap with subtree minimum and lazy affine transformations. A recurrence step is implemented by a global decrement, repeated leftmost-zero deletion plus multiplication by 2 of its right suffix, then an appended \(2^{D+1}\). These operations implement the stated recurrence **exactly**; there is no floating-point arithmetic. Each step requires expected \(O((1+D)\log m)\) treap operations. The pseudorandom seed only changes the tree's internal balancing, not the answer.

Build and reproduce:

\`\`\`bash
g++ -std=c++17 -O3 fast_lifetime.cpp -o fast_lifetime
./fast_lifetime 32750
./fast_lifetime 1000 --dump    # exact far-to-near positive lifetime vector
\`\`\`

At the authentic F421 secondary seed, the normalized input is
\`[327661,14,30,6,22,14,1,2]\`. After **32750** cycles the evaluator reports **8215 normalized cells**, **24543 deleted cells**, and the deletion-count histogram:

\`\`\`
0:16835 1:10692 2:3391 3:994 4:444 5:164 6:169 7:36
8:14 9:3 10:5 11:1 12:1 13:1
\`\`\`

First 10 final lifetimes:
\`294911 70272 135808 4736 86656 37504 168576 37504 103040 627328\`.

Last 10:
\`46 14 22 14 30 6 22 14 1 2\`.

The independent Python recurrence implementation was used to compare the **entire exact list**, not only counts, at cycles 0,1,2,3,10,100,500,1000, all matching. On the local shell the event-driven evaluator took about 0.06 seconds at 32750 cycles (machine-specific observation). A \`--dump\` scalar check gives final lifetime weighted mass of bit length 8218, with SHA-256 of its canonical decimal string \`2d045cbf4b54a1e0114b944a645d82ab7a09493db53825857f8fbb9057bbd94d\`.

## Formal status and use

\`F421SecondaryLifeIter.lean\` proves the exact 32750-cycle **original-source** P-profile as \`physicalP 4 (lifeIter 32750 firstLives)\`; \`F421SecondaryBlankFar.lean\` proves its connection to the real blank tape. \`F421SecondaryLifeCount.lean\` proves the relation between the source cell-count powers and the normalized lifetimes. Therefore a **future kernel-checkable certificate that \`(lifeIter 32750 firstLives).length = 8215\`** would also prove the primary body length 8217. As written the C++ measurement of 8215 is experimental arithmetic, not a Lean numeric certificate.

The source-to-tertiary transition after the secondary zero remains an open proof obligation.
