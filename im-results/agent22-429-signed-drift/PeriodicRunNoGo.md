# All eventually periodic F-run schedules are impossible in the #429 signed inverse model

**Status: complete paper-level argument, not yet independently peer-reviewed or fully Lean kernel-certified.** The independent arithmetic pieces [PeriodicGridPacking.lean](PeriodicGridPacking.lean) and [AffineOrbitRigidity.lean](AffineOrbitRigidity.lean) compile in Lean 4.36.0-rc2 with standard axioms only. The missing formal step is the **original-model periodic-word and rotation-to-grid connection**; the theorem for authentic signed paths is therefore not yet kernel-certified. This is a universal structural no-go for *hypothetical infinite paths* in the established signed compressed inverse model. It is **not** a decision of #429's authentic blank orbit or BB(6). It strictly strengthens the older [constant-run obstruction](ConstantRunObstruction.md): the run lengths may follow *any* finite periodic pattern, rather than one fixed value.

## Statement and exact model

In the admissible safe region \(u>0,D\ge2,D\ne4\), with the established signed Bad guards, the compressed inverse blocks are:

\[
\begin{array}{c|c|c|c}
 &\text{guard}&u'&D'\\ \hline
F&u\equiv0\pmod2&u/2&D+3u+3\\
E\ (=EF)&u\equiv1\pmod2,\ D\equiv0\pmod8&u+(D+8)/8&D/4+4\\
S\ (=SF)&u\equiv0\pmod2,\ D\equiv4\pmod8&u+(D+20)/8&D/4-1
\end{array}
\]
The rank \(R=6u+D\) grows by 3, 10, 14 respectively. The previously source-checked signed-drift and F-run-parity proofs establish: an infinite admissible path contains infinitely many F and E/S blocks; the number \(m_i\) of F blocks between successive E/S pairs is even; and the next pair type is **unchanged** for \(m_i\equiv2\pmod4\), **switched** for \(m_i\equiv0\pmod4\). See [SignedFRunParity.lean](../agent18-429-root-invariants/SignedFRunParity.lean), [SignedDrift restoration](README.md), and [ConstantRunObstruction.md](ConstantRunObstruction.md).

**Theorem.** For any such infinite admissible signed path, its pair-to-pair even F-run length sequence \((m_i)\) is **not eventually periodic**. This applies to all hypothetical branch-29, branch-13 and branch-15 infinite signed paths. It does not rule out an aperiodic infinite path.

## Mathematical proof

**1. Period selection.** Assume the even integers \((m_i)\) eventually repeat. Discard a finite prefix, and choose a primitive period for \(j_i=m_i/2+1\ge1\) containing \(a\) letters and digit length \(t=\sum_{i=1}^a j_i\). The pair type is deterministically toggled if and only if \(j_i\) is odd. Thus the combined pair-type/length word has period **one or two** copies of this primitive \(j\)-period. Not every \(j_i\) can equal 1, because an infinite signed path has infinitely many F blocks. In particular \(t>a\).

**2. Exact integer-affine rigidity.** At an arbitrary pair-input phase of one *combined* period, let \((u_n,D_n)\) be the states after \(n\) complete periods. Let \(C>0\) be the total rank increment. Then \(R_n=R_0+nC\). Both pair blocks have first-coordinate linear part \(u\mapsto u/4+R/8\); each F divides its first coordinate by 2. Hence the period recurrence is
\[
u_{n+1}=\lambda u_n+A R_n+B,\qquad
\lambda=4^{-J}\in(0,1),\quad A>0,
\]
where \(J\) is the sum of all \(j_i\) in the combined period. The exact solution has shape \(u_n=s n+b+c\lambda^n\), with \(s=AC/(1-\lambda)>0\).

Since \(u_n\in\mathbb Z\), the *integer* differences \(u_{n+1}-u_n\) converge to \(s\), forcing \(s\in\mathbb Z\). Similarly \(u_n-sn\) are integers converging to \(b\), so \(b\in\mathbb Z\); the remaining integers \(c\lambda^n\to0\) vanish eventually, hence \(c=0\). Therefore every pair-input phase is an **exact integer arithmetic progression** \(u_n=s_i n+b_i\), and \(D_n=(C-6s_i)n+d_i\).

Its E/S type fixes the parity of \(u_n\) and the residue of \(D_n\bmod8\) for every \(n\). Therefore \(s_i=2v_i\) for an integer \(v_i>0\), and \(8\mid C-6s_i\). Consequently \(C=4K\), \(K>0\) integral, and positivity of \(D_n\) for all \(n\) implies \(0<v_i/K\le1/3\). The additive E/S constants disappear upon taking period slopes. Pair+F-run slope transport gives
\[
2v_{i+1}=\frac{2v_i+(C-12v_i)/8}{2^{m_i}},
\quad\text{i.e.}\quad
\boxed{v_{i+1}=\frac{v_i+K}{4^{j_i}}}.
\]
Set \(x_i=v_i/K\). Then \(x_{i+1}=(x_i+1)/4^{j_i}\). This recurrence depends on \(j_i\), not on the pair type. Its one-primitive-\(j\)-period map is an affine contraction of ratio \(4^{-t}\), and its square fixes \(x_i\) when the types toggle. A contraction whose square fixes a point already fixes that point; hence \(x_i\) is periodic after **one** primitive \(j\)-period.

**3. Pure base-4 digits and denominator packing.** The slope recurrence constructs a purely periodic radix-4 expansion of \(x_0\), using one digit 1 followed by \(j_i-1\) zeros for each gap. Its minimal digit period is precisely \(t\): a shorter digit period would induce a shorter cyclic period in the gaps between successive digits 1, contradicting the primitive \(j\)-period. There is at least one zero (since \(t>a\)) and at least one one.

Reduce \(x_0=p/q\). The slope representation \(x_0=v_0/K\) gives **\(q\mid K\)**. Periodicity of its base-4 digits gives \(q\mid4^t-1\), so \(q\) is odd. Its \(t\) distinct cyclic digit rotations are distinct fractions \(r/q\), all with digits 0 or 1. Every rotation lies in
\[
U=(0,1/12)\ \cup\ (1/4,1/3).
\]
Indeed a first digit zero bounds the value strictly between 0 and \(0.0\overline1_4=1/12\); a first digit one bounds it strictly between \(1/4\) and \(0.\overline1_4=1/3\), using the presence of both digits.

**Odd-grid lemma.** For odd \(q>0\), the number of \(r\in\{1,\ldots,q-1\}\) with \(r/q\in U\) is at most \(\lfloor(q-1)/6\rfloor\). To check exactly, write \(q=12h+\rho\) for \(\rho=1,3,5,7,9,11\). The counts of gridpoints in the first/second interval are respectively
\[
(h,h),\quad(h,h),\quad(h,h),\quad(h,h+1),\quad(h,h),\quad(h,h+1).
\]
Thus \(t\le\lfloor(q-1)/6\rfloor\), giving the universal lower bound
\[
\boxed{q\ge6t+1}.
\]

**4. Rank budget contradiction.** One pair with \(m_i=2(j_i-1)\) subsequent F blocks contributes rank increment \(6j_i+4\) if E, or \(6j_i+8\) if S.

If one primitive \(j\)-period is already type-periodic, write \(e+s=a\) for its E/S counts. Then
\[
C=6t+4e+8s,\quad K=\tfrac32t+e+2s
\le\tfrac32t+2a\le\tfrac72t<6t+1.
\]
If the types require two primitive periods, the second copy interchanges every E and S. Hence each of the \(a\) letters is E once and S once:
\[
C=12t+12a,\qquad K=3(t+a)\le6t.
\]
In both cases \(K\le6t\), contradicting \(q\mid K\) and \(q\ge6t+1\). **QED.**

## Scope, reproducibility and missing quantifier

This is a **general mathematical proof for the compressed signed model**, building on the existing checked model/compression/parity lemmas. The argument itself is not yet a compiled original-source Lean theorem. Independent [periodic_slope_obstruction_check.py](periodic_slope_obstruction_check.py) exhaustively validates all primitive base-4 gap words of length at most 17 and both E/S initial types: 261,554 type cycles with no denominator/rank exception. The finite computation is corroboration, not a replacement for the unbounded proof.

A full Lean formalization would certify this new model-level universal structural theorem. Even then, **aperiodic** sequences of mixed F-run lengths remain possible candidates and the source-machine blank-root halting question remains open. Further finite schedules or fixed residues do not close the remaining infinite-path quantifier.


### Exact finite-word half-rank transfer (Lean)

The added [PeriodicMacroTransfer.lean](PeriodicMacroTransfer.lean) represents a paired E/S block followed by \(m=2(j-1)\) F blocks as an exact half-rank macro:
\[
4^j u'=u+r+c,\qquad r'=r+3j+a,\qquad r=(6u+D)/2,
\]
with \((c,a)=(4,2)\) for E and \((10,4)\) for S. PeriodicMacro.transfer proves by induction that every fixed finite typed word has an affine input/output transfer \(M U=u+A r+B\), \(R=r+T\). PeriodicMacro.periodic_word_is_affine then applies the kernel-certified discrete rigidity theorem to any repeated word, returning an exact integral slope and its defining relation. These two claims compile locally with standard axioms. This source-independent algebra closes the **word-to-affine** part of the proof, not the original signed-to-macro bridge or the primitive digit-rotation construction.
