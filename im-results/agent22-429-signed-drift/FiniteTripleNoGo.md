# Finite triple-repeat obstruction for signed #429 inverse macro paths

**Status: new paper-level finite-pattern theorem with its exact affine-forcing component Lean-checked.** The complete primitive-word-to-rotation step has not yet been source-integrated into Lean; the theorem is conditional on the established compressed signed model, not a decision of the authentic blank-root #429 machine or BB(6).

## Claim: sufficiently long primitive cubes cannot occur

Consider a finite segment of a safe signed inverse path that consists of **three consecutive identical copies** of a nonempty typed pair/F-run word \(W\). Each macro is one E or S pair followed by \(m_i=2(j_i-1)\) F blocks, with \(j_i\ge1\). Suppose \(W\) is the shortest period in *paired type and run length* arising from a primitive \(j\)-word of \(a\) letters, digit length \(t=\sum j_i\), with at least one \(j_i>1\). Since a period of the \(j\)-word either preserves or toggles pair type, the typed word \(W\) consists of **one or two** primitive \(j\)-periods.

Define the half-rank and macro constants
\[
r=3u+D/2,\quad
\begin{cases}
4^{j_i}u'=u+r+4,\quad r'=r+3j_i+2 &(E),\\
4^{j_i}u'=u+r+10,\quad r'=r+3j_i+4 &(S).
\end{cases}
\]
Let \(C>0\) be the total half-rank increment across one copy of \(W\), \(J\) the total digit length of \(W\) (\(t\) or \(2t\)), and \(M=4^J\). At the start let \((u_0,r_0)\) be the first pair input. Then **a necessary condition for such a triple repetition is**
\[
\boxed{4^J\ \le\ 2\left\lfloor\frac{r_0+2C}{3}\right\rfloor.}
\]
Equivalently, if the finite typed word is long enough that \(4^J>2\lfloor(r_0+2C)/3\rfloor\), three consecutive copies are mathematically impossible. Unlike the eventual-periodicity obstruction, this concerns a **finite path prefix** and can therefore constrain genuinely aperiodic paths.

## Proof

**1. Finite affine transfer.** The Lean-certified module [PeriodicMacroTransfer.lean](PeriodicMacroTransfer.lean) proves that any typed word has an integer-affine transfer
\[
M u'=u+A r+B,\qquad r'=r+C,
\]
where \(A>0\) for a nonempty word and \(M=4^J\). At four period boundaries of a triple word, write the first coordinates \(u_0,u_1,u_2,u_3\). The three exact equations are
\[
\begin{aligned}
M u_1&=u_0+Q,\\
M u_2&=u_1+AC+Q,\\
M u_3&=u_2+2AC+Q,
\end{aligned}\qquad Q=A r_0+B.
\]
Since every pair input lies in the safe region \(D\ge2\), \(3u\le r\); since the boundary half-ranks are \(r_0,r_0+C,r_0+2C\), the first three coordinates are at most \(H=\lfloor(r_0+2C)/3\rfloor\).

The Lean-certified theorem [FiniteTripleRigidity.lean](FiniteTripleRigidity.lean), instantiated by [FiniteTripleMacro.lean](FiniteTripleMacro.lean), proves that **if \(M>2H\)** then
\[
u_0+u_2=2u_1,\qquad (M-1)(u_1-u_0)=AC.
\]
The discrete mechanism is exact: subtract the three transfers to obtain
\[
M(u_3-2u_2+u_1)=u_2-2u_1+u_0.
\]
The right side is an integer with absolute value at most \(2H<M\), so divisibility forces the second difference to be zero. The displayed affine slope is \(u_1-u_0=AC/(M-1)>0\).

**2. Propagate integer slopes through the word.** At every paired position \(i\) in the first two copies of \(W\), define \(s_i=u_i^{(1)}-u_i^{(0)}\), and similarly the difference across copies 1 and 2. The boundary affine identity makes these differences equal at phase zero. Subtracting the same macro equations in the two copy pairs gives the same update for both differences:
\[
4^{j_i}s_{i+1}=s_i+C.
\]
They therefore remain equal at every intermediate phase. At the end of the word the next phase is the original phase, and \(s_{\mathrm{end}}=s_0\). The positive start slope and this recurrence make all \(s_i\) positive integers.

**3. Convert to a primitive radix-4 cycle.** Pair type at a fixed phase is the same in copies 0 and 1. The E/S parity guards force \(s_i\) even, and fixed residues of \(D=2r-6u\bmod8\) imply \(2C-6s_i\equiv0\bmod8\), so \(C\) is even. Write \(s_i=2v_i>0\), \(C=2K>0\). Then the finite cyclic slopes obey
\[
4^{j_i}v_{i+1}=v_i+K.
\]
The recurrence has the unique fixed cycle associated with the primitive \(j\)-word; in the doubled typed-period case the same contraction argument shows that the normalized \(v_i/K\) values repeat already after one primitive \(j\)-period. Thus their radix-4 digits have one 1 per run-length gap \(j_i\) and zeros between 1s. Because that gap word is primitive and contains at least one \(j_i>1\), its shortest base-4 digit period is exactly \(t\), with both digits 0 and 1 present. The \(t\) distinct cyclic digit rotations are fractions \(z/K\) with \(z\in\{1,\ldots,K-1\}\), each in the two disjoint windows
\[
(0,1/12)\ \cup\ (1/4,1/3).
\]
The all-denominator [Lean grid-packing theorem](PeriodicGridPacking.lean) gives \(K\ge6t+1\).

**4. Rank budget.** If the full typed word is one primitive \(j\)-period, writing \(e+s=a\) for its pair types gives \(C=3t+2e+4s\), so
\[
K=C/2\le\tfrac72t<6t+1.
\]
If the typed word requires two primitive gap periods, the second interchanges E and S and \(C=6t+6a\); hence \(K=3(t+a)\le6t\). Either way \(K\le6t\), contradicting \(K\ge6t+1\). The assumption \(M>2H\) is therefore impossible. QED.

## Scope and what it enables

The two new exact finite-repetition results, PeriodicTriple.three_periods_force_affine and PeriodicMacro.triple_word_slope, were compiled locally with Lean 4.36.0-rc2; both report only standard axioms, no sorryAx. The **full finite primitive-cube no-go remains paper-level** because the primitive digit-word rotation construction and the original F/EF/SF source bridge have not yet been kernel-checked.

This strengthens the structural agenda beyond proving that ultimately periodic paths cannot occur: an aperiodic infinite path must avoid all sufficiently large triple powers of its primitive paired run-length words relative to the half-rank at their occurrence. This does **not** exclude cube-free aperiodic words and does not close #429 or BB(6). The useful next attack is to combine this quantitative finite-word exclusion with source-rooted residue/valuation guards, rather than running more finite periodic schedules.
