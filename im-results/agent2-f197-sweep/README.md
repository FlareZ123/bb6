# F197 exact reductions and blank-root nonhalting certificate

**Current strongest result:** [exact positive self-embedding and blank-root certificate](NonhaltingCertificate.md), reproducible using [verify_nonhalt.py](verify_nonhalt.py). The literal F197 machine reaches the cylinder B(P^72 HEAD L^80 l,e), l beginning1, after a literal seed and 181 accelerated epochs. Every configuration in this cylinder has a strictly positive return to the same cylinder, independently of the opaque suffix. The exact computer-assisted proof is complete, locally verified in 11.45s. Full source-connected Lean trace and Raw132 Cover remain pending; do not change the authoritative canonical roster yet.

New general-purpose source proof modules: [PrefixCheck](PrefixCheck.lean), [EpochMarker](EpochMarker.lean), [EpochMarkerExit](EpochMarkerExit.lean), [EpochEntrance](EpochEntrance.lean), [EpochMarkerBulk](EpochMarkerBulk.lean), [CounterCore](CounterCore.lean). The last module lifts arbitrary finite local cores over unbounded counters, including non-AA terminal and J/U/C marker configurations. The older infinite-language closure strategy is superseded for this literal root by the self-embedding cylinder.

## Historical exact reset-family results

**Strongest theorem (Lean, original source machine):** [arbitrary mixed P/Q reset monoid](ATFreeMonoidTheorem.md) for any nonempty W∈{P=AAT,Q=TAT}⁺, nonempty A/T data `c₀...c_q`, Z=c₀(Tc₁)...(Tc_q), Φ=A H(c₀)...H(c_q), H(A)=AT,H(T)=AAT, F(P)=P,F(Q)=AAAT, and any aligned left continuation X:
```
B(W Z AA X,e) → B(F(W) Φ X,e)
steps = 68·#P + 82·#Q + 74 + 68q + 14·#T(data)
```
Both the exact source run and **strict +2 finite-bit growth** are kernel-certified under Lean 4.36.0-rc2, only `[propext, Quot.sound]`, no sorryAx. Proof files: [ATFreeMonoidCore.lean](ATFreeMonoidCore.lean), [ATFreeMonoid.lean](ATFreeMonoid.lean), [ATFreeMonoidGrowth.lean](ATFreeMonoidGrowth.lean), and [ATGeneralParser.lean](ATGeneralParser.lean); CIs [46083890068](https://github.com/FlareZ123/bb6/actions/runs/46083890068) and [46083987937](https://github.com/FlareZ123/bb6/actions/runs/46083987937). This subsumes the prior P^n / complementary TAT counter families, which remain historical intermediate evidence. The earlier open blank-orbit problem is addressed by the certificate above; the universal BB(6) upper bound remains open.

**Strongest source-certified result:** the [unbounded complementary-AT reset family](ATPairedTheorem.md) is a Lean-accepted exact literal-source identity for arbitrary run-aligned suffixes and every finite A/T data list. It gives `TAT Z AA X → AAAT Φ X`, exactly `156+68q+14t` live steps and +2 left bits (Lean run 46080673465, only `propext, Quot.sound`). The [older parametric P-prefix rules](ParametricReset.md) and [Agent31 paired-AA program](../agent31-f197-macro/PairedResetCandidate.md) complement this result. These earlier families alone did not establish blank-root nonhalting.


## Historical sweep and obstruction results

The exact two-sweep reduction and counterexample below remain useful independently; their safety invariant is conditional and must not be mistaken for a Cover.

Use nearest-first stacks with implicit zero tails. D left excludes head, D right includes head; B/F/A left includes head, their right excludes it. In B/F/A omit the guaranteed first right bit (0 in B, 1 in F/A) in the shortened right tail. Initial D stacks after 3 live steps are L=011, R=blank. Agent31's Macro.lean supplies the 13 literal exact macro rules. Combining forced D110/D101 followups yields this complete prefix code:

| R | new L | new R or shortened B tail | state | live steps |
|---|---|---|---|---|
| 01u | 01L | u | D | 4 |
| 111u | 010L | u | D | 5 |
| 110u, L=0v | 0101v | u | D | 13 |
| 1000u | 0110L | u | D | 4 |
| 1011u | 0101L | u | D | 10 |
| 00u, L=0v | v | 01u | B | 6 |
| 1010u | 1L | 01u | B | 12 |
| 1001u | fatal | — | — | 3 live, next query halts |

Every ordinary D code consumes at least 2 bits; finite support ensures reversal or fatal. The B/F/A sweep has parametric blocks (j,k nonnegative, arbitrary suffix), with right prefixes prepended to the shortened tail:

| consumed L | right prefix | result | live steps |
|---|---|---|---|
| (11)^j 0 | 0^(2j) | D | 2j+2 |
| (11)^j 10 1^k 00 | 0 1^(k+1) 0^(2j+2) | B | 2j+k+6 |
| (11)^j 10 1^k 01 | 1^(k+1) 0^(2j+2) | D | 2j+k+7 |

Every D exit prepends 01 to the unconsumed L suffix. All blocks consume left bits; finite support implies termination of B sweep. Output prefixes concatenate in reverse chronological order.

## Unconditional left property

At collapsed D boundaries L starts 01 and every internal zero gap between one runs has length 1 or 2. This holds at the seed. Each ordinary D push preserves it (D110 removes the first zero and increments the old top one run). A left-sweep return is 01 followed by a suffix of L or 1L; a residual internal gap cannot exceed an original gap. In particular an A0 loop with k=0 consumes three consecutive zeros after the preceding one run, forcing blank thereafter, hence the next B0 has j=0.

## Right safety grammar and conditional preservation

Define G for finite words trimmed of trailing zeros: blank permitted; otherwise at most 3 leading zeros, internal gaps 1 or 3, and a singleton one run followed by gap 3 must be the first run with leading-zero count 0 or 1. Ordinary D codes preserve G: 01 and 111 shorten the first run or expose a formerly internal run; 110 removes a two-run and one zero; 1000 removes singleton and gap 3; 1011 removes singleton, gap 1 and two bits of next run. G excludes fatal prefix 1001.

At D reversal 00 the suffix u is blank, starts 1, or starts 01 with formerly first run after 3 leading zeros (so singleton followed by gap 3 forbidden). At reversal 1010, the second singleton was internal, so following internal gap cannot be 3; u is blank or starts 1. In both cases B shortened right tail is 0W, W=1u nonempty leading 1, in H: internal gaps 1 or 3, ALL runs preceding gap 3 have length >=2, including first.

If B entries have <=2 leading ones, then odd B10 uses j=0; even B0 j=0 or 1. An A0 loop with k>=1 transforms W to 1^(k+1)000W, preserving H. If k=0 the left property forces next B0 j=0, so G allows the resulting singleton first run with one leading zero. A final B0 yields 0^(2j+1)W; a final A1 yields 1^(k+1)000W; both belong to G. This gives a sufficient safety argument, but its naive premise is false.

## Actual B3 exception and repair

First B entry with 3 leading ones occurs at zero-based return index 99427, after **3,347,592 live transitions**. Inclusive left prefix:
111001001100110010011001100101011001010101100101100110010101100101011001100101100101
Shortened right tail prefix:
0111100011011110001111100011011110001111100011011110001111100011011110001111100011
There are 84 significant left bits and 1588 significant shortened right bits. Independent literal primitive simulation reproduced state B and these stack prefixes at that time. It is not a halt.

**Repair lemma:** if B has prefix 111001 and shortened tail 0W with W in H, then B11,B10,F0,A1 (9 live steps) give D left L' starting 01, right 100000W. D1000 (4) gives L=0110L', R=00W. D00 (6) gives B left 110L', shortened tail 01W. B11,B0 (4) give D left 01L', right 0001W. All 23 transitions are live. Since 1W has >=2 first ones, right returns to G. This handles any number of such exceptions without assuming they are unique.

Therefore sufficient all-time orbit condition: every B entry has <=2 leading ones or prefix 111001. Equivalently exclude >=4 leading ones and 111 followed by anything other than 001. This is not proved.

Exact accelerated scan (sweep.cjs) through 3,310,000 complete returns, 112,293,468 live steps, 4,955,637 B entries found five B3 events, all prefix 111001: (return index, live count) = (99427,3347592), (107701,3623206), (108548,3650052), (120183,4037204), (171997,5782870). No forbidden B entry or halt in this finite scan.

Negative results: a finite right-only grammar plus unconstrained left projection cannot establish the condition. The nondeterministic left projection admits the sequence D110,D1010,D00 giving B with 111 then blank; right feasibility must be tracked. A coarse right suffix DFA with four-bit head class and exact-left pushdown backward saturation also admits spurious long B runs via invented D110 sequences. Do not retread B<=2 conjecture or present this reduction as a Cover. The remaining safety target is a **relational reset-language invariant** proving that all real blank-tape returns lie in domains of exact safe rewrites, including the complementary AT and J/U/C marker branches. Do not retry independent-stack product grammars: both all-B and grouped-nonblank-B product invariants have finite exact counterexamples in [GroupedProductObstruction.md](GroupedProductObstruction.md).
