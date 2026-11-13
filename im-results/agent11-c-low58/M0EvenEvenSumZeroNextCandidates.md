# m=0 even-even sum-zero: odd-valuation normalization and residual candidates

**Status:** The odd-valuation normalization below has a paper-level derivation from the source-certified parent and inverse lemmas in `M0EvenEvenSumZero.lean`, but its general induction has not been Lean-formalized or CI-checked. The explicit s = 2048w + 293 instance is drafted in `M0EvenEvenSumZeroS293.lean`, with exact-criterion integration in `CThreeDiagonalM0SumZeroS293Full.lean`; the u = 1 low-boundary lemmas are in `M0SmallBoundaryZero.lean`; the x ≡ 2 (mod 16), y = 3 boundary is in `EvenOddThreeX2Mod16.lean`; and the s = 32w + 31 B-parent reduction is in `M0EvenEvenSumZeroS31.lean`. The two even-valuation high-stop families s = 1024w + 229 and s = 1024w + 533 have complete source-Lean drafts in `M0EvenEvenSumZeroS229.lean` and `M0EvenEvenSumZeroS533.lean`; Agent 3 independently checked their affine chains and parent arithmetic. None of these drafts is yet source-certified.

**Validation boundary (13 November 2026):** Runs 43397606989, 43398121845, 43398303602, and 43398653987 all failed in the combined original-source compile step; no green run establishes the new drafts. Run 43397606989 stopped at the x ≡ 2 (mod 16), y = 3 module before reaching them. The separate main-branch run 43399504684, on head `94c54cb5083ab85c11719f32b82541f9eb94be68`, reported “No goals to be solved” at the trailing `omega` in the zero-time branch of `blank_no_y3_xmod16_two`; main now removes that redundant tactic in commit `5b6e32bf1773a12e19570cc0deb93723c94c45c2`. That correction has not yet been rechecked. The first failing declaration in run 43398653987 remains undiagnosed, so do not infer that the later modules passed. The main workflow remains `workflow_dispatch`-only; no push trigger is to be added for validation.

The older `EvenOddThreeX256.lean` unique-parent draft is superseded. The exact source counterexample `secNext (31,115)=some (266,3)` establishes that x ≡ 10 (mod 16) can have an n = 2 parent as well as n = 0; no unique-parent claim is valid in that residue.

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
Both have odd right coordinate and sum \(1\pmod4\). The complete B_s/A_s/high-stop source-exact exclusion is now drafted in M0EvenEvenSumZeroS229.lean: it applies blank_no_sumzero_target, excludes both parents with blank_no_odd_sum_one, excludes L_s with blank_no_L_s_mod8_five, and pulls back through the first two m=0 inverse edges. It is in the manual workflow but has not yet been run.

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
which is odd-right with sum \(1\pmod4\). The complete B_s/A_s/high-stop source-exact exclusion is now drafted in M0EvenEvenSumZeroS533.lean: the direct parent is excluded by blank_no_odd_sum_one, the bounce parent is reduced by two six-even-right inverses to another odd-right sum-one state, and the L_s branch is excluded by blank_no_L_s_mod8_five. It is in the manual workflow but has not yet been run.

## Formalization and remaining obstruction

The general odd-valuation theorem still needs a parametric Lean proof: define the recursive predecessor iterator, prove its closed form by induction, and establish the gate lemma by splitting \(r-n=1\), \(r-n=2\), or \(r-n\ge3\). The \(u=1\) y=0/y=2 fibre is now drafted in M0SmallBoundaryZero.lean, and the \(u=5,r\equiv3\pmod4\) terminal fibre is drafted in EvenOddThreeX2Mod16.lean. The explicit s=293 source proof and exact-criterion integration, plus the s=32w+31 B-parent reduction, are also drafted. All five drafts are in the manual agent11-c-diagonal-late.yml workflow but remain unverified until that workflow succeeds with no sorryAx.

Both even-valuation candidates \(s=1024w+229\) and \(s=1024w+533\) now have complete source Lean drafts in M0EvenEvenSumZeroS229.lean and M0EvenEvenSumZeroS533.lean, respectively. Both are included in the manual workflow but remain unverified until a run completes successfully with no sorryAx. Validation run 43398303602 is in progress on the isolated branch. The residual \(u=5,r\equiv1\pmod4\) y=3 parent fan, the remaining even-valuation cases, and the \(S\equiv0\pmod4\) parent branches remain open. This is a stronger parameterized reduction, not a decision of Machine C or BB(6).


## Supplemental u=5 slices: \(M\equiv0\pmod8\) or \(M\equiv24\pmod{64}\)

The remaining \(u=5,\ r\equiv1\pmod4\) sequence has \(r=201+420M\). A generalized exact y=3 boundary lemma is drafted in EvenOddThreeX128W.lean. For \(w\ge1\), the exact source parents of \((128w+10,3)\) are
\[
P_0=(64w+5,32w+3),\qquad P_2=(16w-1,56w+3).
\]
Both depths \(n=0,2\) are retained; the x=266 counterexample is the case \(w=2\), and is precisely the second parent. Since \(x+6=16(8w+1)\) has 2-adic valuation exactly four and odd factor greater than one, the \(a=1\) bounce branch is impossible; cost parity forces the \(a\ge3\) bounce depth to be even, leaving only 0 and 2.

The second parent has odd right coordinate and sum \(72w+2\equiv2\pmod4\), so blank_no_odd_sum_two excludes it. The first parent has sum \(96w+8\equiv8\pmod{16}\); oddodd_val3_blank_reach_iff forces \((48w+2,40w+1)\). This is an even/odd state with \(x+y+1=88w+4\equiv4\pmod8\), so evenodd_four_blank_reach_iff forces \((44w-1,42w-1)\). The latter is excluded in either of two cases:
- \(w\) even: its sum \(86w-2\equiv2\pmod4\);
- \(w\equiv5\pmod8\): its sum is \(12\pmod{16}\), so oddodd_lowval_blank_reach_iff forces \((43w-3,(85w-7)/2)\), whose odd-right sum is \(1\pmod4\), forbidden by the odd-right image.

Thus blank_no_y3_x128w excludes the terminal whenever \(w\) is even or \(w\equiv5\pmod8\). The earlier \(x=256t+10\) slice is the even-\(w\) specialization, not a unique-parent case.

For the u=5 sequence, the terminal coordinate is \(x=302+512s-4r=16m+10\), where
\[
m=32(s-1)-105M.
\]
When \(M\equiv0\pmod8\), write \(m=8w\), so \(w=4(s-1)-105(M/8)\). The subfamilies covered by the y=3 lemma are:
- \(M=16v\): \(w=4(s-1)-210v\), which is even;
- \(M=24+64z\): \(w=4(s-1)-315-840z\equiv5\pmod8\).

In both cases \(w\ge1\). For \(M=16v\), \(2^r\ge r\) and \(5\cdot2^r=129+211s\), with \(r=201+6720v\), give \(211s\ge876+33600v\ge211(53v+3)\), hence \(w\ge2v+8\). For \(M=24+64z\), \(r=10281+26880z\), so \(211s\ge51276+134400z\ge211(210z+80)\), hence \(w\ge1\).

This excludes two infinite subfamilies of the formerly residual \(u=5,\ r\equiv1\pmod4\) sequence. The generalized Lean module is a draft only: it has been added to the original-source workflow. Validation run 43398303602 is in progress on the isolated branch; the main manual workflow remains unverified. The other \(M\) classes remain open; this does not close the full \(x\equiv10\pmod{16}\) parent fan.