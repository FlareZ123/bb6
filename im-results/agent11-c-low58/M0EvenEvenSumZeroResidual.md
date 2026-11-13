# Machine C m=0 even-even sum-zero residual

**Status: four source-certified infinite high-stop exclusions; the full Machine C decision remains open.**

The standalone original-source Lean module M0EvenEvenSumZero.lean, in namespace BB6.Agent11M0SumZeroVerified, passed Lean 4.36.0-rc2 CI 43383761248. It proves the generic forward parent alternatives for even-even sum-zero targets when S>2 and S%4≠0, the odd-ray two-parent necessity, and four infinite m=0 high-stop exclusions. The printed theorem axiom profiles are [propext, Classical.choice, Quot.sound]; no theorem depends on sorryAx.

This result is a genuine blank-root nonreachability theorem for the exact Machine C section relation. It is not a full Machine C nonhalt proof and does not determine BB(6).

## Exact statement

Let CReach(x,y) denote eventual reachability from the authentic blank-derived section seed (5,1), using the original Machine C section transition secNext. Consider the m=0 high-stop equation

k+j+5 = 4(j+3),

which implies k=3j+7. The following four disjoint infinite families are unreachable:

| j | forced k | equivalent odd parameter t=(j-7)/32 |
| --- | --- | --- |
| 1895+2048v | 5692+6144v | 59+64v |
| 359+8192w | 1084+24576w | 11+256w |
| 5479+16384w | 16444+49152w | 171+512w |
| 10599+32768w | 31804+98304w | 331+1024w |

For every nonnegative parameter in any row, not CReach(2j+3,k).

The four t-cylinders are pairwise disjoint. Within the odd-t parameter ray, their exact natural density is

1/32 + 1/128 + 1/256 + 1/512 = 23/512.

This is a density of excluded parameter values in one m=0 high-stop ray, not a proportion of machines, halts, or BB(6) cases decided.

## Source-parent structure

The exact high-stop predecessor equations first reduce (2j+3,k) to (17+64t,28+96t); mzero_first_two_reach then reduces that configuration to the odd-s residual target

A_s = (130+208s, 94+152s).

The original-source parent extraction theorem m0_odd_ray_parent proves, for odd s, that a blank-root visit to A_s implies a blank-root visit to one of exactly two source-parent candidates:

L_s = (222+360s, 46+76s),
B_s = (54+90s, 127+211s).

This is a forward parent-necessity statement. It is sufficient for the exclusions below; no parent converse is being asserted.

For an even-even target (x,y) with x>0, y≥6, x and y even, x+y=8S, S>2, and S%4≠0, the source theorem even_even_sumzero_parent proves that every source parent is either:

- the direct parent D=(x+y-2,(y-2)/2); or
- the depth-one even-a bounce parent E=(2S-2,(x+2y-2S-8)/2).

The proof uses the complete original-source section_preimage_all_iff grammar. It excludes the a=0 branch because that branch forces S to be a power of two; parity eliminates a=1 and odd-a branches; an even-a bounce depth at least three would force 4|S. The condition S%4≠0 is essential to this two-parent form.

The odd-image invariant excludes any state with x>5, y≥5, y odd, and (x+y)%4=1. The six-of-eight exact inverse equivalence reduces an even-right target whenever y is even and at least six and (x+y)%8 is neither zero nor seven.

## Four exclusion families

### 1. s=32v+29

Here t=2s+1=64v+59 and j=7+32t=1895+2048v. The existing source proof excludes both L_s and B_s using the even-even parent alternatives, the six-of-eight inverse, and the odd-image invariant. The resulting high-stop theorem is high_stop_mzero_j1895.

### 2. s=128w+5

Here t=256w+11 and j=359+8192w. The existing source proof excludes both L_s and B_s; the B_s branch is forced through five six-of-eight inverse transitions to an odd-image forbidden state. The resulting high-stop theorem is high_stop_mzero_j359.

### 3. s=256w+85

The general L-branch theorem blank_no_L_s_mod8_five excludes every L_s with s%8=5. Write s=8q+5. Then

L_s = (2022+2880q, 426+608q),   S=306+436q,   S%4=2.

Its direct parent is (2446+3488q,212+304q), whose forced six-of-eight parent is (2656+3792q,105+152q), an odd-image forbidden state. Its bounce parent is (610+872q,1127+1612q), also odd-right with coordinate sum 1 modulo four. Thus L_s is unreachable for every s congruent to five modulo eight.

For s=256w+85, the B_s branch is

B_s = (7704+23040w,18062+54016w).

Three forced six-of-eight inverses reach the even-even sum-zero target

(39304+117568w,2256+6752w) = (x,y),

with S=(x+y)/8=5195+15540w and S%4=3. The generic parent theorem gives exactly the direct and bounce parents

(41558+124320w,1127+3376w)
and
(10388+31080w,16709+49996w).

Both are odd-image forbidden states. Hence A_s is unreachable. Since t=512w+171, the corresponding high-stop family is j=5479+16384w and k=16444+49152w. The source theorem is high_stop_mzero_5479.

### 4. s=512w+165

Again s%8=5, so L_s is excluded by blank_no_L_s_mod8_five.

The B_s branch is

B_s = (14904+46080w,34942+108032w).

Seven forced six-of-eight inverses reach

(84218+260456w,271+844w),

whose right coordinate is odd and whose coordinate sum is 1 modulo four. The odd-image invariant therefore excludes B_s. Thus A_s is unreachable.

Here t=2s+1=1024w+331, so j=10599+32768w and k=31804+98304w. The source theorem is high_stop_mzero_10599.

## Formal verification

The standalone source module is M0EvenEvenSumZero.lean, namespace BB6.Agent11M0SumZeroVerified. Original-source Lean 4.36.0-rc2 CI 43383761248 compiled the full module, including all four high-stop theorems and their axiom audits. Every printed theorem has axiom profile [propext, Classical.choice, Quot.sound]. The source dependencies copied by the selective workflow are byte-identical between its base revision and the main dependency directories checked for this integration.

The manual-only workflow .github/workflows/agent11-c-diagonal-late.yml now includes the standalone module for future reproducible checks. No always-on workflow was added.

## Remaining mathematical work

- The general even-even sum-zero parent classification for S%4=0 remains open. This is where the exceptional a=0 and deeper even-a bounce branches can occur.
- The odd-s residual outside the four progressions remains open, especially s=7 mod 8.
- The remaining m=0 high-stop parameter ray is infinite; the four cylinders do not cover it.
- The separate modular files M0EvenEvenSumZeroParents.lean, M0EvenEvenSumZeroRays.lean, and CThreeDiagonalM0SumZeroFull.lean remain unverified drafts. The standalone proof run does not certify those files or their combined exact criterion.
- No complete Machine C blank-start decision, BB(6) upper bound, or exact BB(6) value follows.

results/ contains only the concise theorem-level publication note; detailed derivations and experimental context remain in im-results/.

## Next algebraic candidates (not source-certified)

Two further odd-s classes appear to close by the same parent mechanisms: s=1024w+229 and s=1024w+533. Their exact six-of-eight chains, sum-zero targets, direct/bounce parents, and candidate high-stop parameters are recorded in [M0EvenEvenSumZeroNextCandidates.md](M0EvenEvenSumZeroNextCandidates.md). These are algebraically derived only; no Lean proof or CI verification has been completed. Do not include them in the four-family theorem or its 23/512 density until source certification succeeds.
