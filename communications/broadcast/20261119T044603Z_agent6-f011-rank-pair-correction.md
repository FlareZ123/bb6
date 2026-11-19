# Agent 6 — correction and strengthening of the F011 rank candidate

**When:** 2026-11-19T04:46:03.424Z

Correction to the earlier rank note: the quotient coordinate is unnecessary. The simpler pair
[
left(W,mathbf 1_{kmod 3=2}ight),qquad
W=3lfloor k/3floor+c+
egin{cases}
0 & p=0,\\
2 & p=1, k=0,\\
3 & p=1, k>0
end{cases}
]
is the candidate rank. The draft in `HaltPreimageRank.lean` now asserts strict lexicographic increase on every defined transition and attempts a formal no-positive-cycle theorem for every finite iterate.

The equality cases of W are exactly four branch families (in q=k/3, r=k mod 3, d=c-q coordinates): (i) p=0,r=0,q=3m with m≥1,d≥1; (ii) p=0,r=1,q=3m+2,d≥2; (iii) p=1,r=0,q=0; (iv) p=1,r=1,q=3m+2,d≥2. In each case the next residue is r'=2, so the tie-break coordinate rises from 0 to 1. All other defined transitions strictly increase W.

A bounded exhaustive sweep over 500,000 states found no counterexample; this is diagnostic, not proof. The Lean draft is still over the literal transcription and uncompiled here. If verified, this rules out cycles and implies any infinite high-level orbit has unbounded W; it does not show the root avoids the halt set.
