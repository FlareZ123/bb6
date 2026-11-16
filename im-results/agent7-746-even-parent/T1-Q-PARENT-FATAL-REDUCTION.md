# The t=1 Q-parent is an exact fatal ancestor

**Status:** exact algebraic/dynamical reduction; source-Lean integration pending. This is intermediate work, not a proof that the blank root reaches or avoids the parent. Keep in im-results/.

## Statement

Let \(K\) be a genuine first-failure source level and let \(q\) be the actual odd-exit source height after any same-level even resets. Suppose the outgoing odd reset has exponent \(t=1\), with odd \(a,d\) satisfying

\[
a+d=2^{K+2},\qquad 2u+5=9d,
\]

where \(u\) is its child. The exact root/Q parent criterion from [ROOT-QDEPTH-ALIGNMENT.md](ROOT-QDEPTH-ALIGNMENT.md) is

\[
9a+2K+7-2^{K+2}=(2K+7)2^{j+1}. \tag{Q}
\]

Then the child \(u\) is exactly \(j\) even-reset steps before the fatal height

\[
F_{K+2}=4\cdot2^{K+2}-(K+2)-4
       =16\cdot2^K-K-6.
\]

In particular, **any authentic blank-root t=1 Q-parent match forces a fatal hit at level \(K+2\)**. The Q-depth match is not a separate nonfatal branch.

## Proof

Put \(c=2K+7\). The deficit of \(u\) at level \(K+1\) is

\[
D_{K+1}(u)=8\cdot2^{K+1}+K+1-u.
\]

Using \(d=2^{K+2}-a\), \(2u+5=9d\), and (Q),

\[
\begin{aligned}
2D_{K+1}(u)
 &=8\cdot2^{K+2}+2K+7-9d\\
 &=8\cdot2^{K+2}+2K+7-9(2^{K+2}-a)\\
 &=9a+2K+7-2^{K+2}\\
 &=c\,2^{j+1}.
\end{aligned}
\]

Therefore

\[
\boxed{D_{K+1}(u)=c\,2^j.} \tag{1}
\]

The odd-reset sweep-guard theorem supplies all earlier guards through level \(K\).

- If \(j=0\), (1) gives \(D_{K+1}(u)=c=2(K+1)+5\). Hence
  \[
  u=8\cdot2^{K+1}+(K+1)-c
   =16\cdot2^K-K-6
   =F_{K+2}.
  \]
  The child itself is fatal at level \(K+2\).

- If \(j\ge1\), then \(D_{K+1}(u)=2^j c>c\), so \(u\) has first-failure level \(K+1\). Under an even reset at that level, the deficit halves exactly. After \(j-1\) same-level even resets it is \(2c\). Every preceding residual is at least \(4c>2c=4(K+1)+10\), so those resets remain at level \(K+1\). At residual \(2c=4(K+1)+10\), the next even reset exits to level \(K+2\). Its output is
  \[
  8\cdot2^{K+1}+(K+1)-c=F_{K+2}.
  \]
  Thus exactly \(j\) even resets after the t=1 edge reach the fatal height.

The argument uses the exact even-deficit-halving and level-exit criteria in Agent 44's LevelDeficitDynamics.lean; the source-level proof should import those lemmas rather than restating the reset semantics.

## Consequence for the open root problem

The t=1 root/Q-depth intersection is now precisely a root/fatal intersection: if the actual odd-exit source \(q\) satisfies (Q) for any depth \(j\), the deterministic blank-root trajectory halts at \(F_{K+2}\) after the stated finite chain. Conversely, a fatal hit reached by this t=1 edge and its intervening same-level even resets yields (1), hence (Q) and the Q-parent identity.

This does **not** exclude the intersection. The existing exact 100,000-transition audit found no t=1 Q-parent match among 12,246 actual t=1 odd edges, but that remains finite evidence. The all-time question is still whether the blank-root trajectory ever reaches one of these fatal ancestors. Do not count the Q-depth congruence as an independent obstruction once the exact binary equation is imposed.

## Next formalization

Add a source-Lean theorem proving (1), then prove the j-step even chain using even_deficit_halves, even_level_criterion, and even_next_level. The theorem should quantify over the actual odd-exit source height and its first-failure certificate, so it applies after arbitrary same-level even resets.


## Root-source narrowing: at most one even reset before a Q-aligned t=1 edge

There is a useful all-natural reduction for an authentic source history. Let \(p=2^K\), let \(q\) be the actual t=1 odd-exit source at first-failure level \(K\), and put
\[
D=8p+K-q.
\]
The source certificate gives
\[
4p\le q+K+4,\qquad q+K+5<8p.
\]
If the Q-alignment equation holds, the equivalent deficit equation is
\[
18D-32p-20K-34=(2K+7)2^{j+4}>0,
\]
hence
\[
D>\frac{16}{9}p+\frac{10K+17}{9}.
\tag{8}
\]
For the level-entry height \(h_{\rm in}\), the first-failure lower bound gives
\[
D_{\rm in}=8p+K-h_{\rm in}\le4p+2K+4.
\]
If \(q\) occurs after \(m\) genuine same-level even resets from that entry, exact deficit halving gives \(D_{\rm in}=2^mD\). If \(m\ge2\), then
\[
D_{\rm in}\ge4D>
\frac{64}{9}p+\frac{40K+68}{9}
>
4p+2K+4,
\]
a contradiction; the final difference is \((28p+22K+32)/9>0\).

Therefore **a genuine t=1 Q-parent match can occur only at the level-entry state or after exactly one same-level even reset**. Equivalently, its level-entry deficit has 2-adic valuation at most one. This narrows the all-time root/Q intersection from every same-level state to at most two explicit entry deficits per \(K\):
\[
D_{\rm in}\in\{D_Q(K,j),\,2D_Q(K,j)\},\qquad
D_Q(K,j)=\frac{32\cdot2^K+20K+34+(2K+7)2^{j+4}}{18}.
\]
This does not exclude either value. The next root-specific task is to characterize the actual entry-deficit recurrence and show it never equals these candidates (or find a genuine equality).

## Inverse-depth warning

A uniform finite inverse-depth cutoff is not available over the full Q-parent candidate family. The fixed-depth \(j=3402,\ n=887+13122r\) construction in [NESTED-ODD-PARENT-HENSEL.md](NESTED-ODD-PARENT-HENSEL.md) gives, for every finite \(d\), a positive-density 3-adic cylinder of candidates with a \(d\)-edge exact odd-parent chain. Its explicit nine-edge specialization is recorded there. These are synthetic inverse paths, not blank-root paths; the Hensel/band argument is a mathematical derivation and is not yet a standalone Lean theorem.


## Even-entry phase exclusion for large Q matches

The \(m\le1\) result above can be sharpened. For every \(K\ge10\), the level-entry state of a genuine t=1 Q match **cannot have been produced by an even reset from level \(K-1\)**. Hence it must have been produced by an odd reset from some smaller level.

Put \(p=2^K\), \(c=2K+7\), \(X=2^{j+4}\), and \(D_Q=(32p+20K+34+cX)/18\). We have \(D_{\rm in}=2^mD_Q\), \(m\in\{0,1\}\), and \(j+2\le K\), so \(X\mid4p\) and \(X\mid40p\).

Suppose the level entry \(h_{\rm in}\) was produced by an even reset from level \(K-1\). If \(R\) is the predecessor's deficit at level \(K-1\), the exact even-reset formula gives
\[
D_{\rm in}=4p-2+R/2.
\]
For a nonfatal source at level \(K-1\) whose even reset crosses to \(K\), \(R\) is even and \(2K+3<R\le4K+6\). Thus
\[
4p+K\le D_{\rm in}\le4p+2K+1.
\tag{9}
\]

If \(m=0\), (9) gives
\[
40p-2K-34\le cX\le40p+16K-16.
\]
The difference \(cX-40p\) is a nonzero multiple of \(X\): it is divisible by \(X\), and equality would force the odd factor \(c=5\), impossible since \(c=2K+7\ge7\). Hence \(X\le16K+34\). But the lower bound gives
\[
X\ge\frac{40\cdot2^K-2K-34}{2K+7}>16K+34
\]
for all \(K\ge6\). The last inequality holds at \(K=6\), and its difference is increasing thereafter.

If \(m=1\), (9) gives
\[
4p-11K-34\le cX\le4p-2K-25.
\]
Now \(cX-4p\) is a nonzero multiple of \(X\), since \(X\mid4p\) and \(c>1\) is odd. Thus \(X\le11K+34\). The lower bound gives
\[
X\ge\frac{4\cdot2^K-11K-34}{2K+7}>11K+34
\]
for all \(K\ge10\); it holds at \(K=10\) and its difference is increasing thereafter. Both cases contradict the assumed even-produced entry.

Consequently, for \(K\ge10\), every genuine Q match has an odd-reset-produced level entry, so \(h_{\rm in}\equiv2\pmod3\). This is a root-specific phase condition; it does not by itself exclude the surviving odd-entry cases.

For reference, the mod-9 equation fixes \(j\bmod6\) from \(K\bmod18\):
\[
\begin{array}{c|rrrrrr}
K\bmod18&2&3&8&9&14&15\\
j\bmod6&0&0&4&2&2&4
\end{array}
\]
This mod-9 table remains valid.

**Correction: the odd-entry refinement has period 54 in \(K\), not 18.** Put \(c=2K+7\), \(X=2^{j+4}\), and \(W_m=18h_{\rm in}+45\). The exact formulas are
\[
W_0=112\cdot2^K-2K+11-cX,\qquad
W_1=80\cdot2^K-22K-23-2cX.
\]
Since \(W_m\) is odd, \(h_{\rm in}\equiv2\pmod3\) is equivalent to \(W_m\equiv0\pmod{27}\). The term \(2^K\bmod27\) has period 18, while the linear \(K\)-terms have period 27. The full period is therefore \(\operatorname{lcm}(18,27)=54\). The complete necessary table is:

| \(K\bmod18\) | \(K\bmod54\) lifts | \(j\bmod18\), \(m=0\) | \(j\bmod18\), \(m=1\) |
|---:|---:|---:|---:|
| 2 | 2, 20, 38 | 12, 6, 0 | 6, 0, 12 |
| 3 | 3, 21, 39 | 12, 0, 6 | 0, 6, 12 |
| 8 | 8, 26, 44 | 10, 4, 16 | 4, 16, 10 |
| 9 | 9, 27, 45 | 8, 14, 2 | 14, 2, 8 |
| 14 | 14, 32, 50 | 8, 2, 14 | 2, 14, 8 |
| 15 | 15, 33, 51 | 4, 10, 16 | 10, 16, 4 |

The earlier six-column \(K\bmod18\) table omitted two lifts of each residue and is withdrawn. The corrected finite modular table is kernel-checked in [QPhaseTable.lean](QPhaseTable.lean).

**Exact synthetic counterexample to the old table.** Take \(K=26,j=16,m=1\). Then \(c=59\), \(X=2^{20}\), and
\[
W_1=80\cdot2^{26}-22\cdot26-23-2\cdot59\cdot2^{20}
=5,244,976,557\equiv0\pmod{27}.
\]
Thus \(h_{\rm in}=(W_1-45)/18=291,387,584\equiv2\pmod3\), with \(h_{\rm in}+K\equiv2\pmod4\). One even reset gives \(q=414,129,261\), and
\[
B(K,q)=112\cdot2^{26}-2K-34-18q
=61,865,984=59\cdot2^{20}.
\]
So this is an exact \(m=1\), \(j=16\) Q match with \(K\bmod18=8\), whereas the withdrawn table incorrectly listed \(j\bmod18=4\).

The level entry also has an exact odd parent at level 24: \(v_3(W_1)=4\), \(d=64,752,797\), \(P=2d=129,505,594\), and
\[
q_{\rm prev}=2P-8\cdot2^{24}-24-5=124,793,431.
\]
It satisfies the level-24 source certificate and its \(t=1\) reset gives \(h_{\rm in}\). The following one-even/t=1 chain has child \(u=1,069,875,227\) at level 27 with deficit \(59\cdot2^{16}\), so 16 even resets reach \(F_{28}\). All these numerical identities and level certificates are checked in [QPhaseCounterexample.lean](QPhaseCounterexample.lean).

This is a synthetic inverse-grammar witness only: \(q_{\rm prev}\) has not been shown blank-root reachable. It corrects the modular phase classification; it does not produce a root hit or decide #746.
