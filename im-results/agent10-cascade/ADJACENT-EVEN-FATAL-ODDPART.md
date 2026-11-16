# Adjacent-even fatality: valuation cutoff and exact odd-part tests

**Status:** exact arithmetic reduction. The Lean theorem
**adjacent_fatal_source_exponent_le_one** has been added to
**T1QParentFatal.lean** at branch head
**a57c1ea641b252db5d751ceda44896821c784b87**; local compilation is still
pending. The finite root audit is computational evidence only.

## Scope and fatal equation

Fix a source level \(K\). An odd reset has source parameter
\[
P=2^t d,\qquad d\text{ odd},\qquad
6\cdot 2^K+1\le P\le 8\cdot 2^K-1.
\]
Its child \(u\) satisfies
\[
2u+5=3^{t+1}d.
\]

Consider only the **adjacent-even fatal route**: the child is at level
\(K+1\), it undergoes \(r\) same-level even resets, and the next even reset
halts at
\[
F_{K+2}=4\cdot2^{K+2}-(K+2)-4.
\]
The child deficit at level \(K+1\) is therefore \(2^r(4K+14)\).
Substituting \(2u+5=3^{t+1}d\) gives the exact equation
\[
3^{t+1}d+2^{r+1}(4K+14)=32\cdot2^K+2K+7. \tag{1}
\]

This is the special case in which the odd-reset child first enters
\(L=K+1\). More generally, if the child first enters level \(L\ge K+1\)
and then has \(r\) same-level even resets before the final even exit to
\(F_{L+1}\), the exact all-\(t\) equation is
\[
3^{t+1}d+2^{r+1}(4L+10)=16\cdot2^L+2L+5. \tag{G}
\]
The \(t\le1\) cutoff below has only been proved for \(L=K+1\); no
valuation cutoff is claimed for \(L\ge K+2\). Direct odd-output fatality
\(u=F_n\) is a separate all-\(t\) branch.

## Descaling every odd-reset source to a \(t=0\) parameter

There is an exact parameterization that may help organize the remaining
all-\(t\) search. Put \(j=K-t\). Since
\[
6\cdot2^K+1\le2^td\le8\cdot2^K-1
\]
and \(d\) is an integer, division by \(2^t\) gives
\[
6\cdot2^j+1\le d\le8\cdot2^j-1.
\]
Thus the same odd integer \(d\) is a valid \(t=0\) odd-reset parameter
at the lower level \(j\).

Let \(h\) be the source height at level \(K=j+t\), and let \(h_0\) be
the corresponding \(t=0\) source height at level \(j\):
\[
h+8\cdot2^K+K+5=2^{t+1}d,\qquad
h_0+8\cdot2^j+j+5=2d.
\]
Eliminating \(d\) gives the exact affine lift
\[
\boxed{h=2^t h_0+(2^t-1)(j+5)-t.} \tag{D}
\]
If \(u\) is the child of the original \(t\)-reset and \(u_0\) the child
of the corresponding \(t=0\) reset, then
\[
2u+5=3^{t+1}d=3^t(2u_0+5). \tag{D'}
\]

Therefore every odd-reset source candidate \((K,t,h)\) is an affine
lift of a \(t=0\) source candidate at \(j=K-t\), with the same odd
parameter \(d\). This is a parameterization of candidate source states,
not a reachability implication: root reachability of \(h_0\) has not
been shown equivalent to root reachability of \(h\). In these coordinates,
the direct fatal equation becomes \(3^t(2u_0+5)=G(n)\), and the
one-even-exit equation becomes
\[
3^t(2u_0+5)+2^{r+1}(4L+10)=G(L+1).
\]
This may let future work organize the all-\(t\) 3-adic intersection as
a family of scaled \(t=0\) source parameters.

## Fatal histories split at the last odd reset

For a halting trajectory, take \(K\) to be the level of its **last odd
reset**. The remaining tail is even-only. The existing
\(\texttt{no\_even\_then\_even\_fatal}\) theorem in
\(\texttt{SweepNoEvenEvenFatal.lean}\) rules out two consecutive even
level exits in the BB(6) fatal range. Thus the tail has only two shapes:

1. the odd-reset child itself is a fatal state \(F_n\) (direct odd-output
   fatality); or
2. the child first enters some level \(L\ge K+1\), undergoes same-level
   even resets, and the final even exit reaches \(F_{L+1}\), governed by
   the general equation (G).

### Two-level selector for the child level

There is a useful all-\(t\) restriction before solving (G). Put
\(p=2^K\) and \(x=3^{t+1}d=2u+5\). The source band implies
\[
A_{K,t}:=\frac{3^{t+1}}{2^t}(6p+1)
\le x\le
\frac{3^{t+1}}{2^t}(8p-1)=:B_{K,t},
\]
and
\[
\frac{B_{K,t}}{A_{K,t}}
=\frac{8p-1}{6p+1}<\frac43.
\]
The child first-failure level \(L\) is characterized exactly by
\[
G(L)\le x<G(L+1).
\]
For every \(n\ge1\),
\[
3G(n+1)-4G(n)=16\cdot2^n+2n-3>0,
\]
so \(G(n+1)>\frac43G(n)\). If two possible child levels for the same
\((K,t)\) differed by at least two, the corresponding \(x\)-values would
have ratio strictly greater than \(4/3\), contradicting the source-band
ratio above. Therefore:

\[
\boxed{\text{For each fixed }(K,t),\text{ the child level }L
\text{ has at most two possible values, and they are consecutive.}}
\]

This applies to both the direct equation \(x=G(n)\) and the one-even-exit
equation (G). For each candidate \(L\), the latter requires
\[
G(L+1)-x=2^{r+1}(4L+10),
\]
which determines at most one \(r\). Thus the general all-\(t\) fatal
search has at most two child-level/depth candidates for each fixed
source level and odd-reset valuation. The existing
\(\texttt{odd\_entry\_adjacent\_fatal\_depth\_sector}\) theorem in
\(\texttt{SweepOddFatalDepth.lean}\) further forces \(L\bmod6\in\{3,4\}\)
for the one-even-exit branch. For direct odd-output fatality,
\(G(n)\equiv 2^{n+1}+n\pmod3\) forces \(n\bmod6\in\{4,5\}\). Thus the
all-\(t\) candidate levels are the intersection of the at-most-two
consecutive levels with the appropriate fatal sector. This is a scale
reduction, not an exclusion of the remaining \(L\ge K+2\) cases.

### At most one valuation for a fixed fatal target

There is also an all-\(t\) uniqueness statement in the other direction.
Fix \(K\) and a fatal target quantity \(X\), where
\[
X=G(n)
\]
for direct odd-output fatality, or
\[
X=G(L+1)-2^{r+1}(4L+10)
\]
for a one-even-exit fatality. The odd-reset equation is
\(X=3^{t+1}d\), so its source parameter must be
\[
P_t=2^td=\frac{2^tX}{3^{t+1}}.
\]
For successive valuations, \(P_{t+1}=\frac23P_t\). But the source band
\([6\cdot2^K+1,\,8\cdot2^K-1]\) has endpoint ratio strictly less than
\(4/3\), whereas two distinct valuations give a ratio at least \(3/2\).
Therefore **for fixed \(K\) and fixed fatal target \(X\), at most one
valuation \(t\) can satisfy the source band**.

Together, the two-level child selector and this fixed-target valuation
uniqueness turn the general all-\(t\) fatal search into a sparse
intersection problem. They do not by themselves exclude any of the
remaining \(L\ge K+2\) or direct \(t\ge2\) cases.

The direct branch has a useful low-valuation cutoff. Put
\[
G(n)=8\cdot2^n-2n-3.
\]
A direct odd-output fatality satisfies \(3^{t+1}d=G(n)\), and \(G\) is
strictly increasing.

- For \(t=0\), the source band gives
  \[
  18\cdot2^K+3\le G(n)\le24\cdot2^K-3.
  \]
  But
  \[
  G(K+1)=16\cdot2^K-2K-5<18\cdot2^K+3
  \]
  and
  \[
  G(K+2)=32\cdot2^K-2K-7>24\cdot2^K-3.
  \]
  Therefore **direct odd-output fatality is impossible for \(t=0\)**.

- For \(t=1\), the source band gives
  \(3\cdot2^K+1\le d\le4\cdot2^K-1\), hence
  \[
  27\cdot2^K+9\le G(n)=9d\le36\cdot2^K-9.
  \]
  The values at \(K+1,K+2,K+3\) place only \(G(K+2)\) in this
  interval. Strict monotonicity therefore forces \(n=K+2\). This is
  exactly the \(j=0\) direct case of the t=1 Q-parent equation.

Consequently, for the last odd reset before a BB(6) halt:

- \(t=0\) cannot be direct. Its one-even-exit branch is only reduced by
  the results below when the child enters \(L=K+1\); the case \(L\ge K+2\)
  remains open.
- \(t=1\) direct fatality is the \(j=0\) Q-parent case. Its
  \(L=K+1\) one-even-exit branch is the \(j\ge2\) Q-parent case.
- \(t\ge2\) remains possible in the direct equation and in the general
  one-even-exit equation (G) when \(L\ge K+2\). Only the special
  \(L=K+1\) branch is excluded by the \(t\le1\) theorem.

## Valuation cutoff in the special child-level case \(L=K+1\)

Equation (1) and the lower source-band bound imply
\[
3^{t+1}(6\cdot2^K+1)
\le 2^t3^{t+1}d
<2^t(32\cdot2^K+2K+7). \tag{2}
\]
For \(t\ge2\),
\[
27\cdot2^t\le4\cdot3^{t+1},
\]
because writing \(t=s+2\) reduces this to \(2^s\le3^s\). Also
\[
27(6\cdot2^K+1)>4(32\cdot2^K+2K+7),
\]
since the difference is \(34\cdot2^K-8K-1>0\), using
\(2^K\ge K+1\). Multiplying these inequalities yields
\[
2^t(32\cdot2^K+2K+7)
<3^{t+1}(6\cdot2^K+1),
\]
contradicting (2). Hence every adjacent-even fatal history with child level \(L=K+1\) has
\[
\boxed{t\le1.}
\]

The formal source statement is
**adjacent_fatal_source_exponent_le_one** in
**T1QParentFatal.lean**. Its hypotheses are exactly the lower source band
and (1). It does not exclude either remaining valuation, and it does not
restrict direct odd-output fatality.

## Exact odd-part equations for the remaining valuations

For a source height \(h\) at level \(K\), the odd-reset source relation is
\[
h=2^{t+1}d-8\cdot2^K-K-5.
\]
Define
\[
C_t(K,h)=
2^{2t+1}(32\cdot2^K+2K+7)
-2^t3^{t+1}(h+8\cdot2^K+K+5).
\]
Combining this identity with (1) gives
\[
C_t(K,h)=(2K+7)\,2^{2t+r+3}. \tag{3}
\]
The existing adjacent-fatal depth theorem gives \(r\) odd. Thus the
2-adic exponent in (3) is even.

For the two surviving cases, (3) is explicit:

- **\(t=0\):**
  \[
  B_0(K,h)=40\cdot2^K+K-1-3h=(2K+7)2^{r+3},
  \]
  with \(r\) odd, so \(v_2(B_0)\) is even and at least \(4\).
  The source band also gives
  \[
  8\cdot2^K+(2K+7)+3
  \le (2K+7)2^{r+2}
  \le 14\cdot2^K+(2K+7)-3.
  \]
  The ratio of the upper endpoint to the lower endpoint is strictly less
  than \(2\). Hence for each fixed \(K\) there is at most one possible
  power-of-two scale, and therefore at most one \(t=0\) adjacent-fatal
  source height.

- **\(t=1\):**
  \[
  B_1(K,h)=112\cdot2^K-2K-34-18h=(2K+7)2^{r+5}.
  \]
  In the Q-depth notation \(j=r+1\), this is
  \(B_1=(2K+7)2^{j+4}\), with \(j\) even and \(j\ge2\) for the
  adjacent-even branch. The \(j=0\) case is the separate direct
  odd-output fatal case.

Consequently, after the \(t\le1\) cutoff, an adjacent-even fatal source
must pass one of two exact odd-part tests: the odd part of \(B_0\) or
\(B_1\) must be \(2K+7\), with the indicated even 2-adic exponent.
This turns the remaining source question into two explicit arithmetic
conditions on the **actual odd-exit source height**, not merely a
level-entry height.

## The special \(L=K+1,t=0\) candidate cannot enter level \(K\) by an even parent

There is a further root-facing restriction in the BB(6) range \(K\ge266\).
Let \(E\) be the level-\(K\) entry before \(q\) same-level even resets
reach the \(t=0\) odd-exit source \(h\). Write
\[
D_0=8\cdot2^K+K-h,\qquad D_{\rm ent}=2^qD_0.
\]
The entry is nonfatal, so
\[
D_{\rm ent}\le4\cdot2^K+2K+3.
\]
The even-child band from level \(K-1\) is
\[
6\cdot2^{K-1}-1\le E\le8\cdot2^{K-1}-3.
\]
The \(t=0\) equation gives
\[
3D_0=(2K+7)2^{r+3}-16\cdot2^K+2K+1. \tag{4}
\]
The source band gives \(D_0\ge2K+7\), hence \(q\le K-1\).

Suppose \(E\) has an even parent from level \(K-1\). The even-child
band at that level, together with the entry bound above, forces
\[
D_{\rm ent}=4\cdot2^K+\delta,\qquad K+3\le\delta\le2K+3.
\]
Multiplying (4) by \(2^q\) and substituting this expression yields
\[
(2K+7)2^{q+r+3}
=2^{K+q+4}+12\cdot2^K+3\delta-2^q(2K+1).
\]
Since \(q\le K-1\), reduction modulo \(2^q\) shows \(2^q\mid\delta\).
Put \(\delta=2^qe\). Dividing by \(2^q\) gives
\[
(2K+7)2^{r+3}
=16\cdot2^K+12\cdot2^{K-q}+3e-(2K+1). \tag{5}
\]
Here \(1\le e\le2K+3\), so
\[
|3e-(2K+1)|\le4K+8.
\]

The source-band interval for the \(t=0\) fatal depth gives
\[
(2K+7)2^{r+2}\ge8\cdot2^K+(2K+7)+3,
\]
and its upper endpoint gives \(r+3\le K+4\). For \(K\ge266\), these imply
\[
2^{r+3}>4K+8.
\]
Also \(2^q\le\delta\le2K+3\), so
\[
2^{K-q+2}\ge\frac{4\cdot2^K}{2K+3}>4K+8.
\]
The last two elementary growth inequalities follow, for example, from
\(2^K\ge K^3\) for \(K\ge10\).

Now split on the relative exponents.

- If \(r+3\le K-q+2\), the first two terms on the right of (5) are
  divisible by \(2^{r+3}\). Thus \(2^{r+3}\) divides
  \(3e-(2K+1)\), whose absolute value is smaller than \(2^{r+3}\).
  Hence \(3e=2K+1\), so
  \[
  \delta=2^q(2K+1)/3.
  \]
  The bounds on \(\delta\) rule out \(q=0\) and \(q\ge2\). If \(q=1\),
  (5) reduces to
  \[
  (2K+7)2^{r+3}=22\cdot2^K=11\cdot2^{K+1},
  \]
  impossible because \(2K+7>11\) and both odd parts would have to agree.

- If \(r+3>K-q+2\), then \(r+3\ge K-q+3\). Since \(r+3\le K+4\),
  the left side of (5) and \(16\cdot2^K\) are divisible by
  \(2^{r+3}\). It follows that
  \[
  2^{K-q+3}\mid 12\cdot2^{K-q}+3e-(2K+1).
  \]
  Put \(M=2^{K-q+2}\). The expression on the right is \(3M+s\),
  where \(s=3e-(2K+1)\) satisfies \(|s|<M\). Therefore
  \(2M<3M+s<4M\), which is incompatible with divisibility by \(2M\).

Both cases are impossible. Thus **in the special \(L=K+1,t=0\) branch, the level-\(K\) entry
cannot have an even parent from level \(K-1\)**. Any authentic entry into this candidate level must instead
come from an odd reset at some lower level.

This is a paper-level arithmetic derivation; a Lean formalization of this
additional parent exclusion has not yet been added. It is stronger than
the finite parent scan and identifies the next dependency: the incoming
odd-parent family of the unique \(t=0\) candidate at each level.

## Finite blank-root audit

An independent deterministic BigInt reproduction of the blank-root
reset recurrence was run for 100,000 transitions from height \(2\). It
checked the two exact odd-part tests for the special \(L=K+1\) branch
at each actual odd source transition.

| Quantity | \(t=0\) test | \(t=1\) test |
|---|---:|---:|
| Odd source transitions | 24,993 | 12,246 |
| Positive \(B_t\) | 24,993 | 5,260 |
| \(B_t\) divisible by \(2K+7\) | 1 | 1 |
| Quotient a power of two | 0 | 0 |
| Adjacent-even fatal matches | 0 | 0 |

There were 12,474 additional odd transitions with \(t\ge2\), which are
excluded from the adjacent-even branch by the valuation theorem. The run
completed 100,000 transitions without halting, reached level 77,220, and
had maximum observed odd exponent \(16\).

The Python audit **root_forward_3adic.py** has been extended to emit the
same \(B_0/B_1\) statistics under
**adjacent_even_fatal_odd_part_audit**. Its execution in this environment
is still unverified because the local shell and Python tool both returned
client errors; the counts above come from the independent BigInt
reproduction, not from running that Python file.

This is finite computational evidence, not an all-time root nonhalting
proof. In particular, it does not settle the \(t=0\) or \(t=1\) odd-part
conditions for every future root source, and it does not settle direct
odd-output fatality for arbitrary \(t\).

## Next mathematical target

Resolve the general fatal equation (G) for child levels \(L\ge K+2\),
and prove or refute the \(B_0/B_1\) odd-part conditions on authentic
blank-root sources in the special \(L=K+1\) branch. The direct odd-output
branch for \(t\ge2\) also remains open; do not infer its exclusion from
the special-case valuation cutoff.
