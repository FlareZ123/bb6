# TM63 Rst2 odd-prefix q4 cut (computational discovery)

**Status: intermediate computational evidence, not a Lean theorem.** This note records a useful decomposition of the m=2 reset prefix. It belongs in `im-results/`, not `results/`.

## Exact proposed cut

For the original TM63 table, the S1 encoder used by the checked-in counted-reset work, and odd (n), the observed run from
```
s1Config L n 2 a 0 b
```
has a canonical intermediate state at exactly
```
32 + 12*a
```
successful transitions:

- state 4;
- head position 0;
- the right half of the tape is independent of (L,n,a), with (b) entering only as an explicit unary extension;
- for fixed (L,n,a), the left half at this cut is independent of (b).

Writing the head cell as (x=0), the observed right-half pattern is
[
T_{m mid}(x)=1 iff
x=0 ;lor; 1\le x\le4 ;lor; 7\le x\le 9+3b
qquad(x\ge0).
]
Thus the right word is (1^5,00,1^{3(b+1)},00,0^\omega), with the head on its first 1.

From this q4/head-0 intermediate, the observed remaining run takes exactly
[
39+3b
]
steps and reaches
```
s1Config L (n-1) 1 (a+b+2) (2^b-1) 0
```
with final head position (5+3b).

The total is therefore
[
(32+12a)+(39+3b)=71+12a+3b.
]
For odd (n), this is exactly the proposed `resetPrefixCost 2 n a b`, since (v_2(n)=0):
[
48+12(a+v_2(n))+15+4\cdot2+3b=71+12a+3b.
]

## Evidence scope

The deterministic simulator used the literal 12-entry TM63 transition table, sparse bi-infinite tape, and the source-facing S1 encoding:
- (d_0=001), (d_1=111);
- marker (m_2=1101);
- left context (lh=110111);
- right S0 suffix (0,111,00,111^{b+1});
- (operatorname{BinDec}(L,n)) uses the complement (2^{L+1}-1-n), read in 3-bit (d_0/d_1) blocks.

Checks performed:
- q4/head-0 cut time, right-half formula, and b-independence of the left half: (L=5), odd (n\in\{1,3,5,7,9,11,13,15,17,19\}), (a,b\in\{0,1,2\});
- exact suffix endpoint equality with the target S1 configuration: (L=5), odd (n\in\{1,3,5,7,9\}), (a,b\in\{0,1,2\}).

These are finite simulations, not universal proofs. They do not establish any new BB(6) bound or score.

## Why this is preferable to a direct S1-counted-decrement identification

The pinned Rocq source at [SOBCv5.v, TM63 Rst2](https://github.com/ccz181078/busycoq/blob/3f302b87f5fb933c46e97672ffbb6907f373fb6e/verify/SOBCv5.v#L10750-L11283) unfolds `S1,S0,LC`, applies `rw_Bin`, then `es;er`, `LC_Inc`, and a final `es`. The `LC_Inc` interface is a left-counter operation with an arbitrary right context. Its post-rebase state/phase and tape boundary are not definitionally the canonical state-3 S1 input used by `s1Config_counted_decrement`. A direct substitution “inner `BinDec L n` is the counted binary counter, outer `a` is right unary, old `b` is exterior” needs an explicit state/frame bridge; it should not be asserted from the Coq macro name alone.

The q4 cut gives a different, compositional route that avoids that unsupported identification.

## Formal proof plan

1. Split the existing a=b=0 `resetBase_odd_frame` for marker 2 into a 32-step prefix to q4/head 0 and a 39-step suffix.
2. Prove the prefix-to-q4 family for all odd (n) and (a), with arbitrary right exterior. The observed extra cost is (12a); the output right half is fixed and the left half is b-independent.
3. Prove the q4 suffix family with the b-parameterized right word above. Its cost is (39+3b). The suffix does write/finish the left outer-counter encoding, so its left-context/output relation must be stated precisely; do not claim it ignores the left tape.
4. Compose the two theorems to obtain the odd-(n), marker-2 Rst2 prefix.

The checked-in `CountedSweep.lean` left/right sweep theorems are natural components for the 12a and 3b extensions. Until the two frame theorems compile under the original TM63 semantics, keep this as a computational lead only.

## Source-scope clarification from Agent 42

The Rst0/Rst1/Rst2 input has active S0 index (z=0). Coq `LC_Inc` decrements the separate left `BinDec L n) counter; the unary (a) and right (b) are context. Therefore neither branch of the existing positive-(z) S1 counted-decrement theorem applies directly. The q4 decomposition above is an alternative route for the marker-2 odd-(n) case, not a re-use of that positive-(z) theorem.

## Expanded finite screen (2026-11-12 22:22Z)

I broadened the simulator check beyond L=5. Across **702** cases with (L=2,\ldots,8), odd (1\le n<2^L) additionally restricted to (n\le31), and (a,b\in\{0,1,2\}), there were zero failures for all of:
- state 4/head 0 at exactly (32+12a);
- the exact right-half formula on cells (0\ldots40);
- b-independence of the left half on cells (-100\ldots-1);
- exact full-tape equality to the stated S1 target after a further (39+3b) steps.

This remains finite simulator evidence. It strengthens confidence in the cut but does not replace the two quantified frame proofs.

## q4 suffix rewrite: exact finite difference sets

For each of the same 702 cases, I also compared the entire q4-mid tape against the exact target tape. The set of differing cells was independent of (L,n,a) and depended only on (b):
- (b=0): ({5,12,13,14});
- (b=1): ({5,6,7,8,9,15,16,17});
- (b=2): ({5,6,7,8,10,11,12,18,19,20}).

Hence the q4 suffix preserves every cell (x\le4) in all tested cases; its complete tape effect is a right-side rewrite determined only by b. This is strong evidence for a suffix theorem quantified over arbitrary left exterior, with an explicit right-output rewrite. The displayed difference sets are only the b=0,1,2 cases; no general closed form for (D_b) is claimed.
