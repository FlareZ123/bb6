# Machine C: a two-sided all-depth dyadic blank-root obstruction

**Agent 24, 7 November 2026. Status: source-verified intermediate mathematics.** The Machine C halting question and BB(6) remain open. These theorems are proved for the authentic original blank-rooted section and have no finite run-time or inverse-depth cutoff. Do not confuse quotient admission with concrete reachability or claim a complete Busy Beaver upper bound.

## Latest strengthening: all depths, parity-phased source obstruction

**Supersedes the earlier fixed 8-divisibility phase in this document.**
The strongest source-certified theorem is
[AllDepthPhases.lean](AllDepthPhases.lean),
\`BB6.Agent46.expanded_dyadic_all_depth\`:

\[
r\ge8,\quad t\ge7,\quad t\equiv3\pmod4,\quad
b+2=2^rt,\quad x+30t\equiv21+4r\pmod{32}
\quad\Longrightarrow\quad\neg\operatorname{CReach}(x,b).
\]

**Every natural inverse depth r≥8 is covered**, including odd r.
The crucial invariant in \`AlternateDyadic.dyadic_back_iter\` uses
\`(x+2*b)%4=3\`, which suffices for source-unique even-right
predecessors. The explicit terminal residue formula tracks the
accumulated \(4(r-1)\) mass change modulo 32. At r divisible by eight
this recovers the earlier \`ExpandedDyadic.lean\` theorem.

The strongest high-stopping pullback is
[HighAllPhases.lean](HighAllPhases.lean): for every r≥8,
\`r+4≤2*m+2\`, and exact genuine stopping equation
\`k+j+3*m+5=2^(2*m+2)*(j+3)\`, either condition implies
\`¬ CReach (2*j+3) k\`:

| Branch | j modulo 16 | (j+3m+3) modulo \(2^{r+4}\) |
|---|---|---|
| A | \(2r\) | \(9\cdot2^r\) |
| B | \(12+2r\) | \(13\cdot2^r\) |

All displayed j congruences are modulo 16. The older source theorems
\`HighAllDepth.lean\` and \`HighOtherBranch.lean\` are the special
case r divisible by eight, not the frontier. The stronger
[PhaseResidual.lean](PhaseResidual.lean) proves a complete exact
\`RunHalts\` equivalence removing both all-r high stopping
subfamilies from the original two-family stopping criterion.
This is a lossless sieve, **not a nonhalting decision**.

**Unmodified-original-source Lean CI verification:**
[run 42336114356](https://github.com/FlareZ123/bb6/actions/runs/42336114356)
certifies the all-r phase inverse cone;
[run 42336235089](https://github.com/FlareZ123/bb6/actions/runs/42336235089)
certifies both high parameter families and the combined
halting equivalence. The CI compiles original
\`CLine\` / \`secNext\` / full inverse / blank-root bridge sources.
Final audits use only standard foundational axioms, with no
\`sorryAx\`, \`native_decide\`, or model stubs.

At inverse depth r=9, examples admitted by the independently
reproduced M512 overapproximation are:
- Branch A: (j,m)=(2,4265), section target projection (7,510,0).
- Branch B: (j,m)=(14,2213), section target projection (31,510,0).

Both pairs satisfy the exact all-r arithmetic hypotheses and produce
actual immediate stopping inputs. Abstract quotient admission is
numerical evidence of a finite quotient's insufficiency; the original
source Lean proof supplies true blank nonreachability.

**Arithmetic density (separate paper derivation, not a Lean theorem):**
For fixed r, each branch selects one j residue mod16 and exactly
one m residue mod \(2^{r+4}\), because 3 is invertible mod powers
of two. The two branches are disjoint for the same r (their j
residues differ by 12 mod16); different r are disjoint because the
equation gives exact 2-adic valuation
\(v_2(j+3m+3)=r\). The width constraint eliminates only finitely
many m values for fixed r. Summing the disjoint classes gives
limiting natural density among \((j,m)\) pairs in expanding squares:

\[
\sum_{r=8}^\infty \frac{2}{16\cdot 2^{r+4}}
=\frac1{16384}.
\]

The valuation-r tail is bounded by the congruence
\(2^R\mid j+3m+3\), giving a uniform upper-density bound \(2^{-R}\);
this justifies exchange of the density limit and infinite sum.
This is a density of **excluded syntactic high stopping parameter
pairs**. It implies no proportion of Turing machines has been solved.

---

## Main theorem

Let \(\operatorname{CReach}(x,b)\) mean reachability by the unmodified Machine C section transition \`secNext\` from \((5,1)\), at an arbitrary natural time. [ExpandedDyadic.lean](ExpandedDyadic.lean) proves

\[
r\ge8,\quad r\equiv0\pmod8,\quad t\ge7,\quad t\equiv3\pmod4,\quad
b+2=2^rt,\quad x+30t\equiv21\pmod{32}
\quad\Longrightarrow\quad\neg\operatorname{CReach}(x,b).
\]

This covers two distinct terminal residues \(t\equiv3,7\pmod8\). It extends the earlier \`AlternateDyadic.lean\` branch, which required \(t\equiv7\pmod8\) and \(x\equiv3\pmod{16}\). The new \(t\equiv3\pmod8\) branch has \(x\equiv11\pmod{16}\).

### Exact predecessor proof

The structural source theorem [TerminalBroad.lean](TerminalBroad.lean) proves that every source predecessor of any target satisfying

\[
X\equiv3\pmod8,\qquad Y\equiv4\pmod8,\qquad
X+Y+1\equiv24\pmod{32},\qquad Y\ge12
\]

must have right counter \(k\ge5\), odd \(k\), and \((a+k)\equiv2\pmod4\).
The original blank section's odd-right image invariant excludes every such predecessor at positive times; the initial \((5,1)\) is excluded directly. Thus the entire exceptional terminal rectangle is genuinely blank-unreachable for all times.

The proof uses \`complete_section_inverse\`, the full source-specific inverse criterion encompassing the direct affine branch and **every** recursive bounce depth. The last exceptional bounce depth \(n=1\) is eliminated by a sum/cost congruence; the higher depths are divisible by \(16\), contradicting the target's \(8\bmod16\) sum. No finite enumeration substitutes for this inverse argument.

For arbitrary \(r\) the reusable \`dyadic_back_iter\` in [AlternateDyadic.lean](AlternateDyadic.lean) transports a hypothetical actual blank-root occurrence back along the unique affine inverse branches, maintaining

\[
a_i+2b_i+4(r-i)=x+2b,\qquad b_i+2=2^it.
\]

At \(i=1\), \((A,2t-2)\) belongs to the terminal rectangle. This yields the contradiction regardless of the size of \(r\).

## Two new high stopping subfamilies

For high immediate stopping inputs, the original section stopping relation is exactly

\[
k+j+3m+5=2^{2m+2}(j+3),\qquad (x,k)=(2j+3,k).
\]

The source-certified theorems [HighAllDepth.lean](HighAllDepth.lean) and [HighOtherBranch.lean](HighOtherBranch.lean) give **all-time nonreachability** under either of these parameter restrictions, for any \(r\ge8\) with \(r\equiv0\pmod8\) and \(r+4\le2m+2\):

| Branch | Restriction on \(j\) | Restriction on \(j+3m+3\) |
|---|---|---|
| A | \(j\equiv0\pmod{16}\) | \(\equiv9\cdot2^r\pmod{2^{r+4}}\) |
| B | \(j\equiv12\pmod{16}\) | \(\equiv13\cdot2^r\pmod{2^{r+4}}\) |

Branch B requires a proof that the derived odd quotient \(t\ge7\), given by the original stopping equation and the exponential lower bound. This matters because the exceptional target \((3,4)\) is a genuine small boundary case and must be excluded from the universal terminal-root claim.

[HighExplicitFamily.lean](HighExplicitFamily.lean) makes Branch A constructive for \`j=0\` and \`m=3*2^r-1\`; it exhibits the actual natural stopping counter, proves blank nonreachability with no conditional stopping equation, and proves that \`exceptionalIndex\` strictly increases. Thus there are infinitely many **distinct genuine immediate stopping inputs** eliminated by the theorem.

[HighResidual.lean](HighResidual.lean) strengthens the original \`BB6.Agent15.blank_halts_iff_two_parametric_families\` to a **lossless halting equivalence** with both high branches removed. It preserves the low stopping family unchanged. The remaining candidate domain is unbounded, and this iff does not decide Machine C.

## Verification and independent comparisons

The manual-only [source verification workflow](../../.github/workflows/agent24-c-exceptional-dyadic.yml) checks Lean **4.36.0-rc2** against the unchanged \`BB6CLine.nextC\`, exact \`secNext\`, genuine blank reachability bridge, full source inverse, odd-image invariant, and the SectionPower/BlankParam stopping formalization.

- [CI run 42335237015](https://github.com/FlareZ123/bb6/actions/runs/42335237015): complete original-source build passes both expanded terminal and high branch theorems.
- [CI run 42335343727](https://github.com/FlareZ123/bb6/actions/runs/42335343727): complete original-source build passes \`blank_halts_iff_expanded_high_sieve\`.
- Each resulting \`#print axioms\` reports only \`propext\`, \`Classical.choice\`, \`Quot.sound\` (some purely arithmetic facts need fewer). The proofs do not introduce \`sorryAx\`, \`native_decide\`, or unvalidated reachability axioms.

An independent M512 abstract-graph census, transcribing the source physical transition relation, reproduces the previously reported **27,858,704 reached abstract vertices** and **221,572,376 transitions**. Both illustrative high stopping inputs below project to **abstract-admitted** quotient cells:

| \(j,m,r\) | Genuine high stopping section input | M512 projection | Abstract admitted |
|---|---|---|---|
| \(0,767,8\) | \((3,\ 3\cdot2^{1536}-2306)\) | \((3,254,0)\) | Yes |
| \(28,1099,8\) | \((59,\ 31\cdot2^{2200}-3330)\) | \((59,254,0)\) | Yes |

The second example uses \(j=28\) to satisfy the Branch B \(j\bmod16=12\) requirement, and \(28+3\cdot1099+3=3328=13\cdot256\). The projected first coordinates differ. They are not direct abstract-reachability exclusions; the exact source inverse theorem proves actual nonreachability. The existing reproducible M512 algorithm is [QuotientRectCensus.cpp](../agent19-c-odd-dyadic/QuotientRectCensus.cpp); the extra cells were independently queried using the same abstract transition and encoding. This is **experimental** and is not an axiom of any Lean theorem.

The earlier Agent19 alternating dyadic source theorem excludes x-residue \(7\bmod8\) at even inverse depth, while the present cone covers x-residue \(3\bmod8\) at depths divisible by eight. At the representative pairs, the earlier guard is not met. Formal proof that every new parameter escapes **all** other accumulated sieves is a separate comparison task; do not claim such global nonredundancy without that check.

## Open direction

The key unsolved step is an unconditional argument about the infinite residual blank-root search. Combining these new exclusions with the strongest time-free \`ValSix\` and \`C58\` criteria, checking all existing restrictions for concrete novel witnesses, and discovering stronger inverse structures across the remaining sum-seven source branches are useful next tasks. None currently supplies a universal BB(6) upper bound.
