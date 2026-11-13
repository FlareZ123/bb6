# m=0 even-even sum-zero: odd-valuation normalization and residual candidates

**Status:** The first theorem below has a complete paper-level derivation from the source-certified parent and inverse lemmas in M0EvenEvenSumZero.lean, but its **general induction has not yet been Lean-formalized or CI-checked**. The explicit s=2048w+293 instance now has a Lean draft in M0EvenEvenSumZeroS293.lean, its exact-criterion integration is drafted in CThreeDiagonalM0SumZeroS293Full.lean; the u=1 low-boundary lemmas are drafted in M0SmallBoundaryZero.lean; and the x=2 mod 16 y=3 boundary is drafted in EvenOddThreeX2Mod16.lean; and the s=32w+31 B-parent reduction is drafted in M0EvenEvenSumZeroS31.lean. All five files were added to the existing manual agent11-c-diagonal-late.yml workflow, which has not yet been run on these commits. Nothing here is in results/. Candidates 5 and 6 remain algebraic drafts. Do not report any of these extensions as source-certified until the original-source workflow passes with no sorryAx.

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
u=1\ \text{or}\ u\ge7\ \text{or}\ (u=5\land r\equiv3\pmod4).
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
This identity follows by induction from \(129+211s=2^r u\). Put \(q=r-n\). For \(u\ge5\), every \(n<r\) has an even right coordinate at least \(8\), so the six-even-right size and parity hypotheses hold. The \(u=1\) case uses only the steps with \(q\ge3\), as handled separately below.

It remains to check its modulo-eight gate. The coordinate sum at depth \(n\) is
\[
310+512s-2^q u-4n.
\]
For \(u\ge7\), then for every \(n<r\) the right coordinate is even and at least \(12\). The modulo-eight check is: if \(q\ge3\), the sum is \(6-4n\pmod8\), hence \(6\) or \(2\); if \(q=2\), it is \(2-4n\pmod8\), hence \(2\) or \(6\); if \(q=1\), then \(n=r-1\) is even because \(r\) is odd, and \(2u\equiv2\pmod8\), so the sum is \(4\pmod8\). Thus all \(r\) six-even-right predecessor steps are licensed. The terminal state is
\[
T^r(B_s)=(312+512s-2u-4r,\;u-2),
\]
whose right coordinate is odd and at least \(5\), and whose sum is \(310+512s-u-4r\equiv1\pmod4\). This contradicts **blank_no_odd_sum_one**.

If \(u=1\), apply the same six-even-right gate only while \(q=r-n\ge3\). These steps are all licensed: the right coordinate is \(2^q-2\ge6\), and the sum is \(6-4n\pmod8\in\{2,6\}\). At depth \(r-2\), the state is
\[
T^{r-2}(B_s)=(312+512s-4r,\;2).
\]
The exact low-boundary source fibre says every original section predecessor of a target \((x,2)\) is \((x+2,0)\), while no original section transition outputs a right coordinate \(0\). Hence this depth-\((r-2)\) state is also unreachable. The y=0/y=2 fibre lemmas are now formalized in M0SmallBoundaryZero.lean and added to the existing manual agent11-c-diagonal-late.yml source audit. That workflow has not yet been run on this commit, so this boundary strengthening is not yet kernel-verified.

If \(u=5\) and \(r\equiv3\pmod4\), the same \(r\) six-even-right steps are licensed (the terminal right coordinate is \(3\)). The terminal state is
\[
(x,3),\qquad x=302+512s-4r.
\]
Since \(s\equiv5\pmod8\) and \(r\equiv3\pmod4\), \(x\equiv2\pmod{16}\). The q=1 gate uses \(2u=10\equiv2\pmod8\), and the q=2 and q>=3 gates are the same as above. The exact source lemma **blank_no_y3_xmod16_two** in EvenOddThreeX2Mod16.lean shows that every source of such a y=3 target is the unique parent \((x/2,(x+2)/4)\), which has odd right counter at least \(5\) and coordinate sum \(2\pmod4\); **blank_no_odd_sum_two** excludes that parent. This file is included in the manual workflow but has not yet been CI-checked.

In all three cases \(B_s\) is unreachable. \(\square\)

Since \(s\equiv5\pmod8\), the quotient \(S=28+45s\) for \(A_s\) is odd, greater than two, and nonzero modulo four. The source-certified theorem **blank_no_sumzero_target** applies to \(A_s\): its direct parent is \(L_s\), and its bounce parent is \(B_s\). Both are now excluded. Therefore \(A_s\) is unreachable under the same hypotheses.

**High-stop consequence.** Write \(t=2s+1\), \(j=7+32t=39+64s\), and \(k=28+96t=3j+7\). The m=0 stopping equation is exactly \(k+j+5=4(j+3)\). The source-certified first-two-inverse theorem **mzero_first_two_reach** maps reachability of the high target \((2j+3,k)\) to reachability of \(A_s\). Consequently every high-stop candidate satisfying the displayed odd-valuation hypotheses is blank-unreachable.

This is a parameterized 2-adic exclusion, not a finite cutoff. In the exact six-sector criterion it can be represented by excluding
\[
m=0,\quad j=39+64s,\quad s\equiv5\pmod8,\quad
\exists r,u:\ 129+211s=2^r u,\ r\text{ odd},\ u\equiv1\pmod4,\bigl(u=1\lor u\ge7\lor(u=5\land r\equiv3\pmod4)\bigr).
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
This cylinder is disjoint from the four existing source-certified cylinders and from candidates 5 and 6. Its concrete source proof is drafted in M0EvenEvenSumZeroS293.lean, with exact-criterion integration in CThreeDiagonalM0SumZeroS293Full.lean; both are included in the manual workflow, pending CI.

The nested 2-adic cylinders generated by successive even valuations begin as follows (the displayed residue is for \(s\), with modulus \(2^{d+5}\)):
| \(d=v_2(148+211q)\) | \(s\) residue | odd quotient \(u\) at the residue |
|---:|---:|---:|
| 0 | \(29\pmod{32}\) | 781 |
| 2 | \(5\pmod{128}\) | 37 |
| 4 | \(165\pmod{512}\) | 273 |
| 6 | \(293\pmod{2048}\) | 121 |
| 8 | \(4901\pmod{8192}\) | 505 |
| 10 | \(23333\pmod{32768}\) | 601 |
| 12 | \(97061\pmod{131072}\) | 625 |

Thus the d=6 cylinder is the first new one after the three already-certified odd-valuation cylinders; the d=8,10,12,... cylinders form a further nested tail. The entire tail d>=6 has density \(1/1536\) among all s, while the complete odd-valuation family has density \(1/24\). Combined with the separate even-valuation cylinder \(s=256w+85\), the proposed union has density \(35/768\), compared with \(23/512\) for the four currently certified cylinders. This is a small density gain, but the value is the reusable 2-adic normalization and its unbounded family, not the percentage alone.

For the full odd-valuation condition, write \(s=8q+5\). Then
\[
129+211s=8(148+211q).
\]
If \(d=v_2(148+211q)\), then \(r=d+3\). For each even \(d\), the condition that the odd quotient be \(1\pmod4\) selects exactly one residue class of \(q\pmod{2^{d+2}}\), of density \(2^{-(d+2)}\). Summing over even \(d\ge0\) gives density
\[
\sum_{d\text{ even},\,d\ge0}2^{-(d+2)}=\frac13
\]
within \(s\equiv5\pmod8\), hence density \(1/24\) among the odd-t high-stop parameters \(t=2s+1\). The residual quotient is \(u=5\), an infinite but zero-density sequence rather than a finite set. It forces \(5\cdot2^r=129+211s\), hence \(2^r\equiv68\pmod{211}\). Since \(2\) has order \(210\pmod{211}\) (\(2^{105}\equiv210\), \(2^{70}\equiv196\), \(2^{42}\equiv107\pmod{211}\)) and \(2^{201}\equiv68\pmod{211}\), the odd exponents are exactly \(r\equiv201\pmod{210}\), with \(s=(5\cdot2^r-129)/211\) and \(s\equiv5\pmod8\). The new x=2 mod 16 y=3 theorem closes the \(r\equiv3\pmod4\) half of this sequence (equivalently \(r\equiv411\pmod{420}\)). The remaining \(r\equiv1\pmod4\) half (equivalently \(r\equiv201\pmod{420}\)) has terminal \(x\equiv10\pmod{16}, y=3\); its multiple even-depth y=3 parent fan remains open. From the exact source grammar, its \(a\ge3\) parents have even depth \(n=2m\) and
\[
a=\frac{x+6}{2^{2m+1}}-3,\qquad
k=\frac{x-a+1-6m}{2},
\]
for those \(m\) for which the displayed quantities are integral and \(a\ge3\). For this residual sequence, \(r\equiv201\pmod{420}\) implies \(r\equiv0\pmod3\), \(2^r\equiv1\pmod3\), and \(s\equiv2\pmod3\); hence \(3\mid x+6\). Thus the \(a=1\) exceptional branch \(x+6=2^n\cdot16\) is impossible. For this residual sequence, the valuation is explicit. Substituting \(s=(5\cdot2^r-129)/211\) gives
\[
x+6=\frac4{211}(640\cdot2^r-211r-265).
\]
For \(r\ge201\), \(v_2(211r+265)<r+7=v_2(640\cdot2^r)\), so
\[
v_2(x+6)=2+v_2(211r+265)
=4+v_2(10669+22155t),\qquad r=201+420t.
\]
Thus the valuation permits \(\lfloor v_2(x+6)/2\rfloor=2+\lfloor v_2(10669+22155t)/2\rfloor\) even depths, unbounded along 2-adically nested values of \(t\). Since \(3\mid x+6\), the odd part is at least \(3\), so the deepest quotient still gives \(a\ge3\); for these enormous \(x\), the cost formula also gives \(k\ge1\) at every permitted depth. The x=2 mod 16 lemma eliminates the depth fan when \(v_2(x+6)=3\), but the x=10 mod 16 case has \(v_2(x+6)\ge4\) and genuinely allows multiple even depths.

The remaining \(u=5\) sequence still has zero density (at most one q for each valuation d), so the density \(1/24\) is unchanged. This density statement describes only this m=0 parameter sieve, not a fraction of machines or halting runs.

## A new B-parent reduction on the \(s\equiv7\pmod8\) side

For \(s=32w+31\), write
\[
B_s=(54+90s,127+211s)=(2844+2880w,6668+6752w).
\]
Its sum is \(8S\) with \(S=1189+1204w\equiv1\pmod4\), so the source-certified generic sum-zero parent theorem applies. Both parents are excluded:

- The direct parent is \(D=(9510+9632w,3333+3376w)\). It is even/odd with \((D_x+D_y+1)\equiv4\pmod8\), so **evenodd_four_blank_reach_iff** forces its unique parent \(P=(6419+6504w,4875+4940w)\). This \(P\) has odd right coordinate at least \(5\) and sum \(2\pmod4\), excluded by **blank_no_odd_sum_two**.
- The bounce parent is \(E=(2376+2408w,6897+6988w)\). Its right coordinate is odd at least \(5\) and its sum is \(1\pmod4\), excluded by **blank_no_odd_sum_one**.

Consequently **blank_no_B_s31** in M0EvenEvenSumZeroS31.lean proves
\[
\neg CReach(2844+2880w,6668+6752w).
\]
The file is added to the manual agent11-c-diagonal-late.yml workflow but is not yet CI-checked. This is only a B-parent reduction: for the corresponding \(A_s\) target, the parent theorem still leaves \(L_s\), and this note does **not** claim the full \(A_s\) or high-stop family is excluded.


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

The general odd-valuation theorem still needs a parametric Lean proof: define the recursive predecessor iterator, prove its closed form by induction, and establish the gate lemma by splitting \(r-n=1\), \(r-n=2\), or \(r-n\ge3\). The \(u=1\) y=0/y=2 fibre is now drafted in M0SmallBoundaryZero.lean, and the \(u=5,r\equiv3\pmod4\) terminal fibre is drafted in EvenOddThreeX2Mod16.lean. The explicit s=293 source proof and exact-criterion integration, plus the s=32w+31 B-parent reduction, are also drafted. All five drafts are in the manual agent11-c-diagonal-late.yml workflow but remain unverified until that workflow succeeds with no sorryAx.

The even-valuation candidates \(s=1024w+229\) and \(s=1024w+533\) have been independently checked algebraically: their finite six-gate chains and terminal parent branches are consistent, and the existing L_s theorem plus the generic even-even parent theorem should complete them. They are not yet Lean-proven. The residual \(u=5,r\equiv1\pmod4\) y=3 parent fan, the remaining even-valuation cases, and the \(S\equiv0\pmod4\) parent branches remain open. This is a stronger parameterized reduction, not a decision of Machine C or BB(6).
