# m=0 even-even sum-zero: odd-valuation normalization and residual candidates

**Status:** The first theorem below has a complete paper-level derivation from the source-certified parent and inverse lemmas in M0EvenEvenSumZero.lean, but its **general induction has not yet been Lean-formalized or CI-checked**. The explicit s=2048w+293 instance now has a Lean draft in M0EvenEvenSumZeroS293.lean, and the u=1 low-boundary lemmas are drafted in M0SmallBoundaryZero.lean. Both files were added to the existing manual agent11-c-diagonal-late.yml workflow, which has not yet been run on these commits. Nothing here is in results/. Candidates 5 and 6 remain algebraic drafts. Do not report any of these extensions as source-certified until the original-source workflow passes with no sorryAx.

## General odd-valuation branch

Let
\[
A_s=(130+208s,\;94+152s),\quad
L_s=(222+360s,\;46+76s),\quad
B_s=(54+90s,\;127+211s).
\]

The source-certified generic parent theorem in M0EvenEvenSumZero.lean reduces reachability of \(A_s\), for odd \(s\), to the two parents \(L_s\) and \(B_s\). The existing theorem **blank_no_L_s_mod8_five** excludes \(L_s\) whenever \(s\equiv5\pmod8\). The following normalization gives a broad new exclusion of the other parent.

**Theorem (odd-valuation B-parent exclusion).** Suppose there are naturals \(s,r,u\) such that
\[
s\equiv5\pmod8,\qquad
129+211s=2^r u,\qquad
r\equiv1\pmod2,\qquad
u\equiv1\pmod4,\qquad
u=1\ \text{or}\ u\ge7.
\]
Then \(B_s\) is not on the genuine blank-origin Machine C section orbit.

**Proof.** Use the exact six-even-right predecessor
\[
T(x,y)=\left(x+y-2,\frac{y-2}{2}\right).
\]
For \(0\le n\le r\), repeated application gives
\[
T^n(B_s)=
\left(312+512s-2\cdot 2^{r-n}u-4n,\;
      2^{r-n}u-2\right).
\]
This identity follows by induction from \(129+211s=2^r u\). Put \(q=r-n\). For every \(n<r\), \(q\ge1\), so the right coordinate is even and at least \(12\), hence satisfies the size and parity hypotheses of the six-even-right source theorem.

It remains to check its modulo-eight gate. The coordinate sum at depth \(n\) is
\[
310+512s-2^q u-4n.
\]
If \(u\ge7\), then for every \(n<r\) the right coordinate is even and at least \(12\). The modulo-eight check is: if \(q\ge3\), the sum is \(6-4n\pmod8\), hence \(6\) or \(2\); if \(q=2\), it is \(2-4n\pmod8\), hence \(2\) or \(6\); if \(q=1\), then \(n=r-1\) is even because \(r\) is odd, and \(2u\equiv2\pmod8\), so the sum is \(4\pmod8\). Thus all \(r\) six-even-right predecessor steps are licensed. The terminal state is
\[
T^r(B_s)=(312+512s-2u-4r,\;u-2),
\]
whose right coordinate is odd and at least \(5\), and whose sum is \(310+512s-u-4r\equiv1\pmod4\). This contradicts **blank_no_odd_sum_one**.

If \(u=1\), apply the same six-even-right gate only while \(q=r-n\ge3\). These steps are all licensed: the right coordinate is \(2^q-2\ge6\), and the sum is \(6-4n\pmod8\in\{2,6\}\). At depth \(r-2\), the state is
\[
T^{r-2}(B_s)=(312+512s-4r,\;2).
\]
The exact low-boundary source fibre says every original section predecessor of a target \((x,2)\) is \((x+2,0)\), while no original section transition outputs a right coordinate \(0\). Hence this depth-\((r-2)\) state is also unreachable. The y=0/y=2 fibre lemmas are now formalized in M0SmallBoundaryZero.lean and added to the existing manual agent11-c-diagonal-late.yml source audit. That workflow has not yet been run on this commit, so this boundary strengthening is not yet kernel-verified.

In either case \(B_s\) is unreachable. \(\square\)

Since \(s\equiv5\pmod8\), the quotient \(S=28+45s\) for \(A_s\) is odd, greater than two, and nonzero modulo four. The source-certified theorem **blank_no_sumzero_target** applies to \(A_s\): its direct parent is \(L_s\), and its bounce parent is \(B_s\). Both are now excluded. Therefore \(A_s\) is unreachable under the same hypotheses.

**High-stop consequence.** Write \(t=2s+1\), \(j=7+32t=39+64s\), and \(k=28+96t=3j+7\). The m=0 stopping equation is exactly \(k+j+5=4(j+3)\). The source-certified first-two-inverse theorem **mzero_first_two_reach** maps reachability of the high target \((2j+3,k)\) to reachability of \(A_s\). Consequently every high-stop candidate satisfying the displayed odd-valuation hypotheses is blank-unreachable.

This is a parameterized 2-adic exclusion, not a finite cutoff. In the exact six-sector criterion it can be represented by excluding
\[
m=0,\quad j=39+64s,\quad s\equiv5\pmod8,\quad
\exists r,u:\ 129+211s=2^r u,\ r\text{ odd},\ u\equiv1\pmod4,\ u\ge7.
\]

### Coverage and a new explicit cylinder

The condition includes three of the four previously certified m=0 cylinders, so it consolidates rather than merely duplicates their proofs:

- \(s=32v+29\): \(r=3,\ u=781+844v\).
- \(s=128w+5\): \(r=5,\ u=37+844w\).
- \(s=512w+165\): \(r=7,\ u=273+844w\).

It does not include \(s=256w+85\), nor the even-valuation candidates 5 and 6. It also gives new cylinders. For example,
\[
s=2048w+293,\quad r=9,\quad u=121+844w
\]
satisfies the theorem, yielding the previously unlisted high-stop family
\[
j=18791+131072w,\qquad k=56380+393216w.
\]
This cylinder is disjoint from the four existing source-certified cylinders and from candidates 5 and 6. Its concrete source proof is drafted in M0EvenEvenSumZeroS293.lean and is included in the manual workflow, pending CI.

For the full odd-valuation condition, write \(s=8q+5\). Then
\[
129+211s=8(148+211q).
\]
If \(d=v_2(148+211q)\), then \(r=d+3\). For each even \(d\), the condition that the odd quotient be \(1\pmod4\) selects exactly one residue class of \(q\pmod{2^{d+2}}\), of density \(2^{-(d+2)}\). Summing over even \(d\ge0\) gives density
\[
\sum_{d\text{ even},\,d\ge0}2^{-(d+2)}=\frac13
\]
within \(s\equiv5\pmod8\), hence density \(1/24\) among the odd-t high-stop parameters \(t=2s+1\). The restriction \(u=1\) or \(u\ge7\) removes only the \(u=5\) exceptional solution for each \(d\), a zero-density set. This density statement describes only this m=0 parameter sieve, not a fraction of machines or halting runs.

## Even-valuation residual candidates

The following two candidates have \(r\) even in the decomposition \(129+211s=2^r u\), so the odd-valuation theorem above does not cover them. They still use the existing \(L_s\) exclusion and the generic sum-zero parent theorem.

### Candidate 5: s=1024w+229

Here \(t=2s+1=2048w+459\), so the high-stop parameters would be
\[
j=14695+65536w,\qquad k=44092+196608w.
\]

The \(B_s\) target is
\[
(20664+92160w,\;48446+216064w).
\]
Five six-of-eight inverse steps give
\[
\begin{aligned}
&(69108+308224w,\;24222+108032w),\\
&(93328+416256w,\;12110+54016w),\\
&(105436+470272w,\;6054+27008w),\\
&(111488+497280w,\;3026+13504w),\\
&(114512+510784w,\;1512+6752w).
\end{aligned}
\]
The last target has sum \(8S\), with \(S=14503+64692w\) and \(S\equiv3\pmod4\). Its direct parent is
\[
(116022+517536w,\;755+3376w),
\]
and its depth-one bounce parent is
\[
(29004+129384w,\;44261+197452w).
\]
Both have odd right coordinate and sum \(1\pmod4\). Formalize the exact generic-parent and odd-image steps before claiming this family.

### Candidate 6: s=1024w+533

Here \(t=2s+1=2048w+1067\), so the high-stop parameters would be
\[
j=34151+65536w,\qquad k=102460+196608w.
\]

The \(B_s\) target is
\[
(48024+92160w,\;112590+216064w).
\]
Three six-of-eight inverse steps give
\[
\begin{aligned}
&(160612+308224w,\;56294+108032w),\\
&(216904+416256w,\;28146+54016w),\\
&(245048+470272w,\;14072+27008w).
\end{aligned}
\]
The last target has sum \(8S\), with \(S=32390+62160w\) and \(S\equiv2\pmod4\). Its direct parent
\[
(259118+497280w,\;7035+13504w)
\]
is odd-image forbidden. Its bounce parent is
\[
(64778+124320w,\;104202+199984w).
\]
That parent has even right coordinate and sum \(4\pmod8\). One six-of-eight inverse gives
\[
(168978+324304w,\;52100+99992w),
\]
with sum \(6\pmod8\); a second gives
\[
(221076+424296w,\;26049+49996w),
\]
which is odd-right with sum \(1\pmod4\). This family also awaits source formalization.

## Formalization and remaining obstruction

The new general theorem should be formalized with a recursive predecessor iterator, an induction proving its closed form, and a gate lemma split by \(r-n=1\), \(r-n=2\), or \(r-n\ge3\). Then compose it with the already source-certified **blank_no_sumzero_target**, **blank_no_L_s_mod8_five**, **blank_no_odd_sum_one**, and **mzero_first_two_reach**. The added (u=1) boundary case also needs the y=0/y=2 fibre statements from SMALL-BOUNDARY.md formalized from the complete source iff. Add the new file to the existing manual agent11-c-diagonal-late.yml workflow and require a successful original-source run with no sorryAx before promoting it.

The even-valuation bounce-parent cases and the remaining \(S\equiv0\pmod4\) states are still open. This is a stronger parameterized reduction, not a decision of Machine C or BB(6).
