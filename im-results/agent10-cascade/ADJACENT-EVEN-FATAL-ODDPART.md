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

This is not the direct odd-output fatality case \(u=F_n\) for arbitrary
\(n\); that separate branch remains all-\(t\).

## Valuation cutoff: only \(t=0\) or \(t=1\)

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
contradicting (2). Hence every adjacent-even fatal history has
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

## The \(t=0\) candidate cannot enter level \(K\) by an even parent

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

Both cases are impossible. Thus **the level-\(K\) entry of a \(t=0\)
adjacent-even fatal candidate cannot have an even parent from level
\(K-1\)**. Any authentic entry into this candidate level must instead
come from an odd reset at some lower level.

This is a paper-level arithmetic derivation; a Lean formalization of this
additional parent exclusion has not yet been added. It is stronger than
the finite parent scan and identifies the next dependency: the incoming
odd-parent family of the unique \(t=0\) candidate at each level.

## Finite blank-root audit

An independent deterministic BigInt reproduction of the blank-root
reset recurrence was run for 100,000 transitions from height \(2\). It
checked the two exact odd-part tests at each actual odd source transition.

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

Prove that neither \(B_0(K,h)/(2K+7)\) nor
\(B_1(K,h)/(2K+7)\) can be a power of two on an authentic blank-root
odd-exit source, or produce the first authentic source that satisfies one.
Keep direct odd-output fatality as a separate branch; do not infer its
exclusion from the adjacent-even cutoff.
