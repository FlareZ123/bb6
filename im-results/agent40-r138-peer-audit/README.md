# Independent peer audit of Sheep's r=138 infinite family (Agent 40, R006)

**Date:** 2026-11-03. **Scope:** source-shaped exact mathematical audit plus an independent, executable finite-arithmetic checker. This is an intermediate validation of [Agent 14's theorem and source dossier](../agent14-sheep-even-inverse/ORIGINAL-INVERSE-BRIDGE-20261103.md). It does not decide Sheep or BB(6). Original-source local Lean certification is reported by Agent 14; this independent audit does **not** claim to have rebuilt its entire Lean archive.

## Exact statements and a stronger structural corollary

The previous original-source local Lean theorem is

\[
\forall k\in\mathbb N,\quad \neg\,\operatorname{EvenReach}(10,2^{138+4860k}).
\]

The two rational intermediate families in its proof have the following *stronger, seed-independent* property, deducible from the same exhaustive original-source first-even edge splitting and the elementary arithmetic checked below:

**Proposition (no incoming even-section edges).** Under the exact Sheep \`EvenEdge\` semantics, for every \(k\ge0\), every even section state \(x\), and every \(y\),

\[
\begin{split}
15y+2=2^{141+4860k}&\implies \neg\operatorname{EvenEdge}(x,y),\\
81y+68=2^{143+4860k}&\implies \neg\operatorname{EvenEdge}(x,y).
\end{split}
\]

This strengthening removes any hypothesis that \`x\` itself is blank-reachable. Its mathematical derivation is below. It has **not** been added as a separately kernel-compiled Lean theorem; it is a proof-level corollary of the source-shaped branch algebra and the independently reproduced finite modular exclusions. It is expected to be straightforward to formalize using the existing Agent14 modules. As a consequence, an even-start orbit can enter either family only if its *initial state itself* is already in that family. Since the genuine start is 10 and neither target is 10, their exclusion is not dependent on additional blank-origin invariants.

## Independent derivation

For a generic nonhalting even source \(x=2^a v\), \(a\ge1\), \(v\ge5\) odd, let \(z=F(x)\), \(z-1=2^hu\), \(u\) odd, and \(y=1+3^h u\). The original source algebra gives

\[
(2^{a+1}+1)v+2a=3+2^{h+1}u.
\]

For the target \(dy+c=2^{n_0+4860k}\), let \(D=d3^h\), \(T=D(2^{a+1}+1)\), \(B=(2a-3)D+2^{h+1}(d+c)\). Then any generic incoming edge forces

\[
Tv+B=2^{n_0+h+1+4860k}. \tag{1}
\]

For the exceptional \(v=3\) branch, the exact identity instead is

\[
3D2^a+Da+2D+2^h(d+c)=2^{n_0+h+4860k}. \tag{2}
\]

These were independently checked against the literal \(F,E\) arithmetic in **2,794** (source, target-parameter) instances. The fully generic and exceptional cases are separate; no special case was silently treated as generic.

**First, restrict \(h\) universally.** For the first child, \(h\ge4\) would imply \(2^{141+4860k}\equiv17\pmod{1215}\), whereas it is always \(827\); \(2^{324}\equiv1\pmod{1215}\) and \(324\mid4860\). Thus \(0\le h\le3\). For the second child, \(h\ge2\) would imply \(2^{143+4860k}\equiv149\pmod{729}\), whereas it is always \(635\); \(2^{486}\equiv1\pmod{729}\) and \(486\mid4860\). Thus \(h=0\) or \(1\).

**Second, eliminate exceptional sources.** Equation (2) is \(A2^a+Da+C=2^N\), \(A=3D\), \(C=2D+2^h(d+c)\), \(N=n_0+4860k+h\). The six rows below give the smallest convenient threshold \(a_0\). For every \(a\ge a_0\), the expression lies strictly between \(2^{a+t}\) and \(2^{a+t+1}\), where \(t=\lfloor\log_2 A\rfloor\). This follows from \(2^t<A<2^{t+1}\), the checked inequality \(Da_0+C<(2^{t+1}-A)2^{a_0}\), and induction using \(D(a+1)+C<2(Da+C)\) for \(a\ge1\). For \(1\le a<a_0\), the expression is strictly less than \(2^{n_0}\), while the right side has exponent at least \(n_0\).

| Child | \(h\) | \(A\) | \(D\) | \(C\) | \(t\) | \(a_0\) |
|---|---:|---:|---:|---:|---:|---:|
| 1 | 0 | 45 | 15 | 47 | 5 | 3 |
| 1 | 1 | 135 | 45 | 124 | 7 | 1 |
| 1 | 2 | 405 | 135 | 338 | 8 | 3 |
| 1 | 3 | 1215 | 405 | 946 | 10 | 1 |
| 2 | 0 | 243 | 81 | 311 | 7 | 6 |
| 2 | 1 | 729 | 243 | 784 | 9 | 3 |

**Third, exclude large generic valuation \(a\).** The six respective cutoffs \(a_0\) are \(8,10,12,14\) and \(11,13\). At the cutoff, the following independently checked base facts hold: \(B\) is odd, \(1<B<2^{a_0}\), and \(2D<2^{a_0}\). Since \(B(a+1)=B(a)+2D\), induction preserves \(1<B(a)<2^a\) at all \(a\ge a_0\). Now \(M=2^{a+1}+1\) divides \(2^N-B\) by (1). But \(2^{a+1}\equiv-1\bmod M\), so \(2^N\bmod M\) is either \(2^r\) or \(-2^r\) with \(0\le r\le a\). A positive odd \(B\) strictly between \(1\) and \(2^a\) equals neither power; also \(B+2^r<M\), precluding the negative case.

**Finally, close every small generic valuation.** For odd \(v\), (1) forces \(2^N+C'\equiv T\pmod{2T}\), with \(C'=2T-B\) when \(B\ge0\) and \(C'=-B\) when \(B<0\). The independent audit includes the one negative-B branch (first child \(h=3,a=1,B=-133\)). Set \(p=\operatorname{ord}_T(2)\) and \(q=p/\gcd(p,4860)\). Because \(N\ge1\), the residue of \(2^N\) modulo \(2T\) has period \(p\) and the sequence with \(k\) has period \(q\). The standalone checker reconstructs and verifies **all 62** \((h,a)\) branches and **all 221** distinct k-period representatives. None satisfy the required congruence. Maximum \(p\) encountered is 6318. These are independently calculated exact integers, without importing Agent14's generator or lookup tables.

All possible original-source even incoming branches are therefore eliminated. The deduction is stronger than a blank-root-only last-predecessor contradiction, but it remains an intermediate structural corollary of Agent14's technique rather than a claim of independent discovery of its residue family.

## Reproduction, verification grade and remaining work

Run \`python audit_r138_independent.py\` (Python standard library). It independently verifies 2,794 exact even-return algebra instances, all 62/221 finite constraints, both universal high-h congruences, six high-a signed gap induction bases, and six exceptional-power interval bases. One should still independently inspect Agent14's reconstructed Lean proof and validate its original-source imports and \`#print axioms\` after GitHub Actions can execute jobs again. The existing manual workflow uses upstream Cryptids at commit \`ced8f9f44f67a167d5ecc03e687b048c67926371\`; its workflow requests Lean 4.35.0-rc4, while Agent14's local successful audit used Lean 4.36.0-rc2. These are explicitly different verification environments.

**Scientific status:** exact independent mathematical branch analysis with executable finite certificates; a seed-independent edge corollary on paper; no new original-source full Lean build by this reviewer; no outside-prior-art novelty certification; no exact BB(6) value or universal machine bound.


## Stronger complete inverse-cone analysis, 15:18 UTC

Let \(R_k=2^{138+4860k}\). Its two candidate even E-parents have **closed forms**

\[
x_{1,k}=\frac{8R_k-2}{15},\qquad
x_{2,k}=\frac{32R_k-68}{81}.
\]

These are genuine integer generic first-even parents for every \(k\ge0\), not only formal solutions of their rational equations. In fact \(R_k\bmod15=4\) because \(138+4860k\equiv2\pmod4\), and \(R_k\bmod81=73\) because \(138+4860k\equiv30\pmod{54}\). Therefore \(v_1=(4R_k-1)/15\), \(u_1=(R_k-1)/3\), \(v_2=(8R_k-17)/81\), \(u_2=(R_k-1)/9\) are positive odd integers with \(v_i\ge5\). The source-generic equations are satisfied with \((a,h)=(1,1)\) and \((2,2)\), respectively. Both parents are distinct.

**New actual local Lean theorem:** [Sheep138ExactParents.lean](Sheep138ExactParents.lean) proves

\`\`\`lean
theorem Sheep138ExactParents.two_generic_parents (k : Nat) :
  ∃ x1 x2 : Nat,
    x1 ≠ x2 ∧
    SheepEvenInverseAlgebra.GenericEdge x1 (R k) ∧
    SheepEvenInverseAlgebra.GenericEdge x2 (R k) ∧
    15*x1+2=2^(141+4860*k) ∧
    81*x2+68=2^(143+4860*k)
\`\`\`

The complete proof was compiled locally under Lean 4.36.0-rc2 with **no holes** and \`#print axioms\` equal to **\`[propext, Quot.sound]\`**. The local prerequisite is an independently copied, literal-equivalent \`GenericEdge\` *definition* from [Agent14's module](../agent14-sheep-even-inverse/SheepEvenInverseAlgebra.lean), with no axioms or assumed mathematics. The committed file imports the real module and awaits a full authentic-import rerun. The theorem explicitly proves generic algebraic source edges; the published source semantics provides the bridge from generic first-even equation to the actual E map, and finite literal E execution checks independently corroborate it.

The [independent exact checker](audit_r138_independent.py) also reconstructs both parents and executes the literal genuine \(F,E\) return for **101** distinct values of \(k\), including \(k=100\) with exponent 486,138: **202** successful checks.

**New source-shaped structural proof texts:**

* [Sheep138NoIncoming.lean](Sheep138NoIncoming.lean) establishes in the original \`EvenEdge\` signature that both rational child families have in-degree zero from every even source.
* [Sheep138RootShield.lean](Sheep138RootShield.lean) derives that every even E-parent of \(R_k\) satisfies one of the two child equations, derives that each genuine E-return lands on an even state, and excludes **any two consecutive E edges** into \(R_k\) from an arbitrary even source.

Both files were individually compiled against **temporary exact-signature interface mirrors** for Agent14's already-published lemmas; the local stub environment naturally prints those upstream signatures as axioms. **This is an interface-level compilation only**, explicitly **not a complete kernel verification of the new claims**. The temporary mocked imports are absent from the committed repository. A full run with the original \`SheepEven\`, \`Sheep138ChildLowCases\`, and \`Sheep138RootCases\` dependency sources is still necessary. The algebraic and finite modular components are independently audited above.

**Mathematical combined result (paper proof, upstream dependent):** Using Agent14's exhaustive source-correct root classification, the independently checked 62 child nonparent cases and the constructive Lean witness theorem, the *exact* incoming first-even-neighborhood of \(R_k\) consists of \(x_{1,k},x_{2,k}\), and both children have zero incoming E-neighbors. Thus its entire inverse E cone has depth one, including both roots and no grandchildren, for every \(k\). Any even-section E trajectory with at least two edges can never reach \(R_k\); the authentic blank start 10 is not equal to \(R_k\) or either child and hence never reaches \(R_k\). The latter global all-time conclusion was already established by Agent14's separately locally source-compiled Lean theorem. This audit now gives the stronger, seed-free structural explanation and the constructive exact two-preimage algebraic witness.

This *complete inverse-cone structure* may be a more reusable presentation of the already-proved r138 family than the purely seed-reachable exclusion. Its standalone independent source-level formal verification and outside academic novelty remain pending.


## Source-level converse and genuine two-parent existence, 15:30 UTC

**Strengthened, independently kernel-checked result:** The algebraic \`GenericEdge\` and \`SpecialEdge\` cases used throughout this source-connected analysis admit full original-source \`SheepEven.EvenEdge\` constructors. Both directions are now formalized in new files:

- [SheepGenericConverse.lean](SheepGenericConverse.lean) proves \`GenericEdge x y → EvenEdge x y\` from the actual \`Step.generic\` constructor, the full affine formula, the oddness and lower bound of \`v\`, and the exact factorization of the intermediate section value.
- [SheepEdgeConverse.lean](SheepEdgeConverse.lean) proves the exceptional \`SpecialEdge x y → EvenEdge x y\` from \`Step.special\`, then unifies both branches into \`Edge x y → EvenEdge x y\`.
- [SheepExactEdgeEquiv.lean](SheepExactEdgeEquiv.lean) independently checks the reverse direction on even sources, giving the fully quantified **if and only if**
  \[
  x\equiv0\pmod2\ \Longrightarrow\
  \left(\mathrm{EvenEdge}(x,y)\iff
  \mathrm{GenericEdge}(x,y)\lor\mathrm{SpecialEdge}(x,y)\right)
  \]
  **without a reachability assumption**.

The last source-equivalence theorem compiled with Lean **4.36.0-rc2**, with \`#print axioms\` equal to **\`[propext, Classical.choice, Quot.sound]\`**. The two converse lemmas print only **\`[propext, Quot.sound]\`**.

- [Sheep138ActualParents.lean](Sheep138ActualParents.lean) imports the universal constructive algebraic witness theorem and the new source-converse lemma to kernel-check the stronger all-k theorem

\`\`\`lean
theorem Sheep138ActualParents.two_source_parents (k : Nat) :
  ∃ x1 x2 : Nat,
    x1 ≠ x2 ∧
    SheepEven.EvenEdge x1 (2^(138+4860*k)) ∧
    SheepEven.EvenEdge x2 (2^(138+4860*k)) ∧
    15*x1+2=2^(141+4860*k) ∧
    81*x2+68=2^(143+4860*k)
\`\`\`

This **actual original-source EvenEdge existence** theorem compiled locally with \`#print axioms [propext, Quot.sound]\`. Crucially the local build here used the **authentic exact upstream archived source bytes** of Agent16's \`SheepEven.lean\` (SHA256 \`82d1b77cbd8d2071b624834de5796697f6d3b02941ecda08d7f0075cbea846d5\`) and \`EvenEdge.lean\` (SHA256 \`11e9b78ee4ddc8dca5538915d2d2773f83741643ad64eaeb6135259d0efe72b9\`). They were reconstructed from \`im-results/agent16-sheep-even-return/SheepEven.lean.xz.b64\` and \`even-reach-lean.tar.xz.b64\`, and compiled independently with standard axioms. The local algebraic module contained verbatim original definitions only, cloned from \`SheepEvenInverseAlgebra.lean\`, as the full repo module could not be mounted into this isolated local shell. No assumed source theorem or stub axiom was used in these certified files; the committed Lean files import the actual original algebraic source module.

The **two-person existence certificate is now fully source-semantic and kernel-checked** as opposed to the earlier purely algebraic witness. The *at-most-two* and *no-grandparent* halves remain paper-proved, backed by the finite modular audit and Agent14 source case lemmas, and await independent full original-source kernel compilation of \`Sheep138NoIncoming\` and \`Sheep138RootShield\`. The original source equivalence theorem is a reusable semantic link for every other rational-exponential reverse-search programme, beyond this single modular family.

All genuine source proof statements have been kept distinct from the interface-stub checking and empirical 202-transition replay.
