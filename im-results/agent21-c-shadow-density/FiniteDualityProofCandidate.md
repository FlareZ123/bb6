# Complete finite-language / modular-cone duality: induction proof candidate

**Status 2026-11-28: mathematical derivation for adversarial review and Lean formalization. NOT yet a source-certified all-depth theorem.** This note records the whole proposed proof, including the two edge cases that a naïve completed-word induction misses: pending singleton words and normalization of signed children. The currently certified source theorem is the uniform all-row density bound in [run 46102569750](https://github.com/FlareZ123/bb6/actions/runs/46102569750).

## Claim to prove

In `BB6.Agent42ModularCone`, for any signed `Pair p=(x,y)`, any bit precision `b∈Nat` and any fuel `f≥b`:

\[
\boxed{\operatorname{check}(f,b,p)=\mathrm{true}
\quad\Longleftrightarrow\quad
\neg\operatorname{OpenAt}(S(x,y),Z(x,y),b).}\tag{D}
\]

The word-language right side is the definition from `DyadicReach.lean`, with signed coordinates
\[
\epsilon=(x+y)\bmod 2,\qquad
Q=x+y+\epsilon,\qquad
S=-x-2y,\qquad
Z=(-x-2-(S\bmod2))/2.
\]
The completed case is a positive-gap list \(w\) with total cost \(b\) and \(2^b\mid Z+\operatorname{acc}(S,w)\). The pending case is a positive-gap list ending in a gap at least 2, with total cost \(b+1\), satisfying the **same** divisibility by \(2^b\). The pending alternative is essential.

Because `excluded b p = check b b (residue b p)`, the corollary of (D), periodicity and residue normalization is
\[
\boxed{\operatorname{excluded}(b,p)=\mathrm{true}
\quad\Longleftrightarrow\quad
\neg\operatorname{OpenAt}(S(p),Z(p),b).}\tag{E}
\]
Here all coordinates are signed, so intermediate inverse parents may be negative. No identification with actual Machine C reachability is made until the source theorem is invoked.

## Lemma 1: exact signed first-letter arithmetic

For every positive gap \(r\), the definition of `offset` gives
\[
Z+\operatorname{offset}(S,r)
 =-x-y-\bigl((-x+3r+1)\bmod2\bigr).\tag{1}
\]
If a word beginning with \(r\) has its numerator zero modulo \(2^b\), then, because the rest of `acc` is multiplied by \(2^r\),
\[
2^{\min(r,b)}\mid Z+\operatorname{offset}(S,r).\tag{2}
\]
When \(b\ge1\), (2) forces the leading number even. Its parity, using (1), is equivalent to
\[
r\equiv y+1\pmod2.\tag{3}
\]
Under (3), the parity term in (1) equals \(\epsilon\), hence
\[
Z+\operatorname{offset}(S,r)=-Q,\qquad
2^{\min(r,b)}\mid Q.\tag{4}
\]
The use of \(\min(r,b)\), rather than assuming \(r\le b\), is important: a pending singleton can have gap \(r=b+1\). The Lean fragments `DyadicGapConstraint.lean` and `DyadicSignedGap.lean` formalize both the ordinary and min-cost versions (compilation pending).

## Lemma 2: when the adjusted sum is b-divisible, a word always exists

If \(b=0\), the empty completed word works. For \(b\ge1\) and \(2^b\mid Q\), choose:
- \([b]\) as the **completed** witness if \(b\equiv y+1\pmod2\);
- \([b+1]\) as the **pending** witness otherwise (its only gap is at least 2).

In both cases (1)–(4) give a numerator equal to \(-Q\), divisible by \(2^b\). In particular `OpenAt(S,Z,0)` and `OpenAt(S,Z,1)` hold for **every** signed pair; \(Q\) is always even. `DyadicSignedOpen.lean` records this constructively (not yet compiled).

## Lemma 3: signed dyadic translation invariance

For \(b\ge1\), an arbitrary signed translation \((x,y)\mapsto(x+2^b u,y+2^b v)\) changes the normalized coordinates by
\[
S'=S-2^b(u+2v),\qquad Z'=Z-2^{b-1}u.
\]
By `DyadicAffine.acc_translate`, for any positive *nonempty* word \(w\),
\[
(Z'+\operatorname{acc}(S',w))-(Z+\operatorname{acc}(S,w))
=-2^{b-1}\bigl(u+(u+2v)\operatorname{coeff}(w)\bigr).
\]
The word coefficient is odd, since its first gap is positive. The bracket is even. Thus the difference is divisible by \(2^b\), proving `OpenAt` is invariant under independent \(x,y\) shifts by \(2^b\). For \(b=0\), `OpenAt` is identically true. The complete/pending equivalence is written in `DyadicPeriod.lean` and `DyadicSignedPeriod.lean` (pending Lean compilation). This lemma legitimizes the executable checker's repeated calls to `residue (b-r)`, rather than exact signed parent values.

## Lemma 4: the exact signed inverse branches

Assume the target has finite exact binary valuation \(v=v_2(Q)<b\), so \(2^v\mid Q\) and \(2^{v+1}\nmid Q\). By Lemma 1 any positive-gap word compatible at precision \(b\) has first gap \(r\le v<b\). Consequently **even a pending word has a nonempty tail**, which is itself a completed/pending word at precision \(b-r\).

The admissible gap costs are *exactly*:

1. **Direct:** \(r=1\), necessarily \(y\) even by (3). Signed parent
   \[
   (x',y')=(x+y-2,(y-2)/2).
   \]
   It has
   \[
   S'=S+4=S+\operatorname{shift}(1),\qquad
   2Z'=Z+\operatorname{offset}(S,1)=-Q.
   \]
2. **High:** \(r=n+2\le v\), with
   \[
   n\equiv x+1+\epsilon\pmod2.
   \]
   Put
   \[
   a=Q/2^{n+1}-2-\epsilon,\qquad
   k=(x+2y-a-7-3n)/2.
   \]
   Since \(v\ge n+2\), the quotient \(Q/2^{n+1}\) is even. The parity condition makes the numerator defining \(k\) even, so both signed coordinates are integers. The source checker therefore has `HighValid=true` **automatically** whenever `Allowed` holds; it is not an extra filter here. Direct algebra gives
   \[
   -a-2k=S+3n+7=S+\operatorname{shift}(n+2),\qquad
   2^{n+2}Z(a,k)=-Q=Z+\operatorname{offset}(S,n+2).
   \]

For any branch cost \(r\), exact word concatenation yields
\[
Z+\operatorname{acc}(S,r::w)
=2^r\bigl(Z'+\operatorname{acc}(S',w)\bigr).\tag{5}
\]
Because \(r<b\), \(2^b\mid\) LHS iff \(2^{b-r}\mid\) the child numerator. The completed case has tail total cost \(b-r\); the pending case has tail total cost \(b-r+1\) and retains the last gap \(\ge2\). Conversely prepend the branch \(r\) to *any* completed or pending child witness; the positive-gap and divisibility requirements are preserved. This is the precise two-sided `OpenAt` recurrence. Its forward direction is already source-certified in `DyadicReach.open_prepend`; the bidirectional divisibility lemma is drafted as `DyadicStrip.word_strip_dvd_iff`.

## Lemma 5: bad case and finite valuation logic

For \(b\ge2\), `Bad p` is equivalent to
\[
y\text{ odd},\qquad Q\equiv2\pmod4\qquad(\text{exact valuation }v=1).
\]
By (3), every first gap of a compatible word must then be **even**, so at least 2; by (4), every first gap must also satisfy \(r\le v=1\), contradiction. Thus `Bad p → ¬OpenAt`. This includes the pending-singleton possibility because (4) uses \(\min(r,b)\).

If `Bad` is false, `ModularCone.valuation b Q` computes the usual exact valuation whenever \(v<b\) and returns \(b\) when \(2^b\mid Q\). Hence `ValValid b p v` is true precisely in the proper finite-valuation case. In the complementary b-divisible case, Lemma 2 yields `OpenAt` and the checker returns false. In the proper case `Allowed p v n` enumerates exactly the high branch costs listed in Lemma 4, plus the direct branch when \(y\) even.

## Induction proving (D)

Use strong induction on bit precision \(b\), simultaneously for *every* integer pair \(p\) and every fuel \(f\ge b\).

- **b=0,1:** the checker is false regardless of fuel (its nontrivial branch requires \(b\ge2\)); `OpenAt` is true by Lemma 2.
- **b≥2, Bad:** the checker returns true and `OpenAt` is impossible by Lemma 5.
- **b≥2, not Bad, not ValValid:** \(2^b\mid Q\), so the checker returns false and `OpenAt` exists by Lemma 2.
- **b≥2, not Bad, ValValid:** the checker is the Boolean conjunction of: (i) the direct child's `check(f-1,b-1,residue...)` when y is even, and (ii) each `Allowed` high child's `check(f-1,b-r,residue...)`. By Lemma 4, all corresponding `HighValid` gates are true and these are **exactly** the possible first gaps of `OpenAt`. Since each \(r\ge1\) and \(f\ge b\), the inductive hypothesis applies at \(b-r\) with fuel \(f-1\). Lemma 3 identifies the normalized residue child with the exact signed parent. Thus the conjunction is true iff **no child has `OpenAt`**, iff the parent lacks `OpenAt` by Lemma 4.

This proves the candidate identity (D), provided the five lemmas and the basic exact-valuation computation are kernel-accepted with the actual definitions. No probabilistic argument is involved; finite tests are *not* part of the proof.

## Consequence for the BB(6) research program (conditional on the Lean bridge)

`DyadicCover.sparse_cover` is already kernel-accepted, and `DyadicSource.source_all_rows_sparse` was original-source certified in run 46102569750. For arbitrary positive denominator \(d\), it produces one modulus \(2^b\) such that, on **every admissible affine family**, the `OpenAt` indices occupy at most \(2^b/d\) residue classes. By (E), the existing **executable modular-cone exclusion checker** certifies every other residue class, i.e. at least the fraction \(1-1/d\), at one precision *uniform in the family*. In the original Machine C system, the existing `reach_open` theorem then excludes actual high-right source configurations outside those residue classes. This is a structural and algorithmic theorem about the global inverse-reachability problem.

It is **not** a Machine C nonhalting proof and not an exact BB(6) result. In particular the stopping-family density theorem alone carries no nonhalting force because the physical blank-root run can encounter at most one stopping state. The actual remaining task is a proof for the exceptional cylinders, or a global argument excluding all stopping parameters.

## Required Lean acceptance gates

1. Source-check `DyadicRays`, `DyadicGapConstraint`, `DyadicSignedPeriod`, `DyadicSignedGap`, `DyadicSignedOpen`, `DyadicStrip`, `DyadicHighValid`, and repair any failures. Manual workflow `agent21-low1875-source.yml` supports separate targets. Do not infer approval from queued runs.
2. Formalize exact truncated valuation and `HighValid` lemma in the original modular-cone source namespace.
3. Formalize the two-sided completed/pending word decomposition in Lemma 4 (the substantive gap).
4. Prove induction on bit budget with sufficient fuel, normalizing every child by `residue`; print axioms. No `sorry` or extra axioms.
5. Connect the certificate-density corollary to `sparse_cover` and original `source_parent`, then include the full proof and a runnable certificate in `results/`.
