# Machine C: fourteen new candidate low-stop cylinders from the complete M16 second-parent sieve

**23 November 2026 · Agent 13 · paper-level original-source argument, not Lean-compiled.** This refines the M16 valuation theorem and Agent 21's exact second-fan profile. It is not a Machine C halt/nonhalt decision. The word "new" below means not already eliminated by the cited Agent 11 low-parameter predicate, its six-sector normalizer, or Agent 21's two first-stop progressions; other work may still overlap.

## Statement and arithmetic residue form

Let \(m=512z+67\), \(z\ge0\), \(K_m=2^{2m+3}-(3m+4)\). The source and quotient argument below excludes blank-section reachability of the target \((1,K_m)\) whenever

\[
\boxed{\ z\bmod64\in\{5,13,29,45,61\}\quad\text{or}\quad z\bmod32=25.\ }
\]

These are **14 disjoint residues modulo 128**, all odd \(z\), equivalently 5 modulo-64 progressions plus one modulo-32 progression. The corresponding low stopping indices are \(m=512z+67\), not \(m=z\). This conclusion is **paper-level pending a single complete Lean source-parent composition**; the finite M16 table theorem itself is source-checked.

## Exact forced prefix to the branching state

Put
\[
 w=2^{2m-1}-(96z+13),\quad K_m=16w+3,\quad
 R_z=(x,y)=((45w-23)/4,(83w-49)/8).
\]
For all \(z\ge0\), \(m\ge67\), \(w\equiv3\pmod{16}\), and all displayed coordinates are nonnegative integers. The checked original-source six-sector normalizer, whose edges preserve blank reachability, performs the **four** unique edges
\[
(1,16w+3)\xleftarrow{O}(8w,12w)
\xleftarrow{B}(20w-2,6w-1)
\xleftarrow{F}(13w-4,(19w-7)/2)
\xleftarrow{O}R_z.
\]
Here the arrow direction is from the halting target to its predecessor; the sequence of inverse guards (in the actual starting-target order) is \(O,B,F,O\), exactly the branches of `SixForcedNormalize.lean`. In particular, blank reachability of \((1,K_m)\) implies blank reachability of \(R_z\). The identities are direct substitutions in the six guards. The first \(O\) uses \(1+(16w+3)\equiv4\pmod{16}\); \(B\) uses \(20w\equiv4\pmod8\); \(F\) uses \(26w-2\equiv4\pmod8\) but not 8 modulo 16; the final \(O\) uses \((45w-15)/2\equiv12\pmod{16}\).

Set \(F(z)=519z+73=2^d q\) with odd \(q\). Then
\[
x+y+1=173\,2^{2m-4}-4F
 =2^{d+2}(173\,2^{2m-d-6}-q).
\]
The estimate \(F<2^{2m-6}\), available for every \(z\ge0\), gives \(d<2m-6\); the parenthesized factor is odd and greater than 1. Hence
\[
v_2(x+y+1)=d+2,\qquad x\text{ even},\quad y\text{ odd},\quad y\ge5.
\]

For the displayed cylinders \(d=2\) or \(3\), so \(x+y+1\equiv0\pmod{16}\), and the normalizer stops at \(R_z\): its odd-low, even-seven, four-sector and even-right guards are all false. Its final exclusion Boolean is false, since \((x+y)\bmod4=3\). Thus **the existing six-sector low test does not exclude any of these 14 cylinders**.

## Exhaustive immediate-parent argument

Apply the existing original-source `BB6.Agent46.complete_section_inverse` (`FullSectionInverse.lean`) to a predecessor \((a,k)\) of \(R_z\). Since \(x\) is even, \(y\) odd, \(x+y\) odd, and \(x+y+1\) has a nontrivial odd factor, the \(a=0\), \(a=1\), direct, and even-\(a\) branches are impossible. The only remaining branch is odd \(a\ge3\), with recursion depth \(n=2r\le d\) even. Its equations force
\[
a_{2r}=\frac{x+y+1}{2^{2r+1}}-3,\qquad
k_{2r}=\frac{x+2y-a_{2r}-7-6r}{2}.
\]
All candidates satisfy the side conditions \(a\ge3\), \(k\ge1\), \(a<2k\) (see `SecondFanExactProfile.md`), and there are exactly \(\lfloor d/2\rfloor+1\) of them. For \(d=2\) and \(d=3\), **there are only \(r=0,1\) parents**. Their coordinates are at least 8, so the finite M16 quotient is determined by their residues modulo 16. The exact arithmetic simplifies to
\[
a_{2r}\equiv-2s_r-3\pmod{16},\quad
k_{2r}\equiv s_r+5-3r\pmod{16},\quad
s_r=(F/2^{2r})\bmod16.
\]
The source-certified M16 `CCert.seen` table, reproduced in `M16SecondFanCensus.md`, has absent residues in row \(r=0\) containing \(s=4,8,12\) and in row \(r=1\) containing \(s=1,5,6,9,11,13,14\).

- **\(d=2\).** \(s_0=4q\bmod16\in\{4,12\}\), so row 0 is always absent. Row 1 has \(s_1=q\bmod16\), absent when \(q\bmod16\in\{1,5,9,11,13\}\). As \(F\equiv7z+9\pmod{64}\), solving \(7z+9\equiv4q\pmod{64}\) gives the five residues \(z\bmod64\in\{5,13,29,45,61\}\).
- **\(d=3\).** \(s_0=8\), absent in row 0; row 1 has \(s_1=2q\bmod16\), absent precisely for \(q\equiv3\pmod4\) (\(s_1=6\) or 14). Solving \(7z+9\equiv24\pmod{32}\) gives \(z\equiv25\pmod{32}\).

Every possible incoming source parent is therefore absent from the kernel-checked M16 quotient, via `CCert.source_reachable_embeds16` and `CCert.reachable_seen`. Since \(R_z\) is not the blank-origin section seed \((5,1)\), reachability would require a previous section state, contradicting the source-certified quotient. This yields the announced all-time exclusion **as a paper argument**. Formalizing this last quantified predecessor/quotient composition, rather than extending the finite census, is the remaining source-acceptance task.

## Exact overlap with already integrated exclusions

The kernel-checked M16 valuation theorem has 38 eliminated residues modulo 128, partitioned as follows (all disjoint):

| Type | \(z\) progression | Residues / 128 | Existing status |
| --- | --- | ---: | --- |
| \(d=0\) | \(z\equiv2\pmod8\) | 16 | Already \(m\equiv1091\pmod{4096}\), Agent 21 first-stop theorem; six-sector also rejects |
| \(d=1\) | \(z\equiv7\pmod{16}\) | 8 | Six-sector normalization pattern \(O,B,F,O,S,O\) ends with odd right and sum 1 mod 4; already rejected |
| \(d=2\) | \(z\equiv5,13,29,45,61\pmod{64}\) | 10 | **Not rejected by existing low predicate or six-sector filter** |
| \(d=3\) | \(z\equiv25\pmod{32}\) | 4 | **Not rejected by existing low predicate or six-sector filter** |

The 14 candidate-new residues all satisfy the older `BB6.Agent11SixAll.lowAllowed` congruence filters: \(m\equiv3\pmod{16}\), \(m\equiv67\pmod{256}\), \(m\not\equiv0\pmod{128}\), and avoid the low C58 and Agent 21 residues. The strictness of the six-sector test follows symbolically from the exact \(O,B,F,O\) normalization and \(x+y\equiv3\pmod4\); this is stronger than a bounded numeric sample. The finite check across 128 residues independently reproduced the stated partition but is not substituted for the unbounded derivation.

## Proof-acceptance handoff

A small new Lean module should import `M16SecondFanValuation`, `FullSectionInverse`, `SixForcedNormalize`, and the accepted `CSourceBridge16`; prove the four-step forced equality, the exact \(r\in\{0,1\}\) parent implication for \(d=2,3\), and discharge both parent cells using existing `CCert.seen` facts and source reachability induction. Compile its complete original-source dependency closure and print the exported axiom profile. No fresh quotient construction or new workflow is needed. Until that passes, **do not call this result Lean-certified or move it into `results/`**.

Source dependencies: [Agent 21 inverse fan](../agent21-c-first-m3mod8/SecondFanExactProfile.md), [Agent 13 certified valuation table](M16SecondFanValuation.lean), [Agent 13 M16 census](M16SecondFanCensus.md), [source complete inverse](../agent3-c-bounce-inverse/FullSectionInverse.lean), [source normalizer](../agent11-c-low58/SixForcedNormalize.lean), [Agent 21 earlier exclusions](../agent21-c-first-m1091-4096/README.md).


## Source-only strengthening: sixteen low-stop cylinders

**Updated 2026-11-23T18:52Z. Paper-level original-source argument; exact generic two-depth inverse theorem now Lean checked in CI [45242048957](https://github.com/FlareZ123/bb6/actions/runs/45242048957). The stopping-family specialization remains to be formally compiled.**

A stronger argument avoids the M16 quotient lookup altogether and adds **two more** uniform cylinders:

\[
\boxed{\ z\bmod64\in\{5,13,29,45,61\}\quad\text{or}\quad
 z\bmod32=25\quad\text{or}\quad z\bmod128\in\{9,21\}.\ }
\]
These are **16 disjoint residues modulo 128** (1/8 of this \(m=512z+67\) subfamily), not 16 individual stopping indices. All 16 pass the previous full low congruence gate and the original target's `sixForcedExcluded` test. Every residue family has \(d=v_2(519z+73)=2\) or 3, hence the only possible immediate parents of \(R_z\) have depth 0 and 2.

The depth-zero parent always satisfies \(k_0\equiv1\pmod4\) and \(a_0+k_0\equiv2\pmod4\), with \(k_0\ge5\); it is excluded by Agent 3's original blank-section odd-image invariant. For the depth-two parent, a *uniform finite source-only normalization* gives:

| Class of \(z\) | Depth-two parent forced normalizer prefix | Terminal odd-right image sum |
| --- | --- | --- |
| \(z\equiv13,29,45,61\pmod{64}\) | empty | \(2\bmod4\) |
| \(z\equiv5\pmod{64}\) | O | \(1\bmod4\) |
| \(z\equiv25\pmod{32}\) | A | \(2\bmod4\) |
| \(z\equiv9\pmod{128}\) | A,O | \(1\bmod4\) |
| \(z\equiv21\pmod{128}\) | O,B | \(1\bmod4\) |

The guards are those *already source-proved* in `SixForcedNormalize.lean`: O is the odd/odd low-valuation inverse edge; A is the even-right affine inverse edge; B is the exact even-right six-source edge. The required terminal right counters are at least five because their starting coordinates grow like positive multiples of \(2^{2m}\), and each fixed-length inverse prefix subtracts only bounded constants and scales by at most 4.

The four direct-rejection rows follow immediately from the exact parent residue formulas \(a_{2r}\equiv-2s_r-3\) and \(k_{2r}\equiv s_r+5-3r\pmod{16}\). The three nontrivial transformation cases use only a few low bits:

1. **\(z\equiv5\pmod{64}\):** the \(n=2\) source parent is \((a,k)\equiv(7,13)\pmod{16}\). It is odd/odd with \(a+k\equiv4\pmod{16}\), so O applies. The next state has odd right coordinate and coordinate sum \(1\pmod4\).
2. **\(z\equiv25\pmod{32}\):** \((a,k)\equiv(1,0)\) or \((1,8)\pmod{16}\), so A applies; the next state has odd right coordinate and sum \(2\pmod4\).
3. **\(z\equiv9\pmod{128}\):** \(a\equiv57\pmod{64}\), \(k\equiv4\pmod{32}\) for the \(n=2\) parent. A gives a parent with coordinates \((11,1)\pmod{16}\); O then gives odd right and sum \(1\pmod4\).
4. **\(z\equiv21\pmod{128}\):** \(a\equiv15\pmod{64}\), \(k\equiv25\pmod{32}\). O gives an even-right state with left coordinate \(2\pmod8\), right coordinate \(4\pmod8\); B applies and reaches odd right and sum \(1\pmod4\).

These are exact modular identities over *every* lift in the stated cylinders. In particular, they use the finite original-source six-sector return theorem, not any `seen=true` or `seen=false` quotient claim. Since each source parent is blank-unreachable by `sixForcedExcluded_sound`, the complete inverse grammar prevents \(R_z\) from being blank-reachable, and the initial four forced edges prevent the stopping target from being blank-reachable.

The **fully source-checked general sublemma** now available at `EvenOddSmallValuation.lean` is `BB6.Agent13SmallFan.even_odd_small_valuation_parent`. It proves all incoming parents for a sufficiently large even-left/odd-right state with \((x+y+1)\bmod64\ne0\) are odd-source bounce parents of depth exactly 0 or 2, preserving the side condition \(a<2k\). The proof imports `FullSectionInverse.lean` and was checked by Lean 4.36.0-rc2 with axioms `[propext, Classical.choice, Quot.sound]`, **no `sorryAx`** (CI 45242048957, before adding the explicit \(a<2k\) conjunct). The follow-on module `EvenOddTwoParentRoot.lean` implements a source-only two-Boolean-parent nonreachability certificate; until its CI passes do not claim that wrapper kernel-verified.

**Research priority:** formalize the above finite modular cylinders against the source-only `two_parent_normalizer_excluded` lemma, then integrate them into the lossless Machine C stopping criterion. No new M16 quotient work is needed. This is still a narrowing of an unbounded existential, not a decision of Machine C or BB(6).
