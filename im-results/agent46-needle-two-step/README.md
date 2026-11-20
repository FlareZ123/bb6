# Two-step even-predecessor bounds for the Space Needle cancellation target

**Status:** exact arithmetic necessary conditions with a paper proof. This is an intermediate result, not a blank-root reachability theorem. It has not been Lean-compiled in this invocation.

## Setup and exact two-step reduction

Write
\[
D_v=2^{v+1}+3,\qquad \beta_v=3\cdot2^v+v+3.
\]
The exact inverse-parent equation at valuation \(v\) is
\[
z=D_v q+\beta_v,\qquad q\in\mathbb N.
\]
It is equivalently characterized by
\[
2z-2v+3=D_v(2q+3).
\]
In particular, if \(z\ge\beta_v\), then \(D_v\mid 2z-2v+3\) is also sufficient: the quotient is odd and at least \(3\), so it is \(2q+3\) for a natural \(q\).

Suppose \(y\) has a predecessor at valuation \(w\ge1\):
\[
y=D_wq+\beta_w,\qquad b=2^w(2q+3).
\]
Here \(b\) is the shifted counter of that predecessor. The parent equation gives
\[
2y-2w+3=D_w(2q+3),
\qquad
b=\frac{2^w(2y-2w+3)}{D_w},
\]
and
\[
y-b=3q+w+3>0.
\]
Thus \(0<b<y\).

Now suppose \(b\) itself has an immediate predecessor at valuation \(t\ge1\):
\[
b=D_tq'+\beta_t,\qquad q'\in\mathbb N.
\]
The exact parent characterization gives
\[
D_t\mid 2b-2t+3. \tag{1}
\]
Eliminating \(b\) and \(q\) from (1) yields
\[
\begin{aligned}
D_w(2b-2t+3)
&=2^{w+1}(2y-2w+3)+(3-2t)(2^{w+1}+3)\\
&=2^{w+2}(y+3-w-t)+9-6t.
\end{aligned}
\]
Consequently every two-step chain satisfies the quotient-free congruence
\[
\boxed{
D_t\mid H_{w,t}(y):=
2^{w+2}(y+3-w-t)+9-6t.
} \tag{2}
\]

This is a necessary condition for all \(w,t\). If \(\gcd(D_t,D_w)=1\), it is equivalent to (1), and hence (provided \(b\ge\beta_t\)) to existence of the second parent. A useful coprimality test follows from
\[
D_w-2^{w-t}D_t=3(1-2^{w-t})\qquad(w\ge t).
\]
Since \(\gcd(D_t,3)=1\), every common divisor of \(D_t,D_w\) divides \(2^{|w-t|}-1\). In particular \(D_t,D_w\) are always coprime when \(|w-t|\in\{1,2\}\).

## Case \(1\le t\le w\): a half-logarithmic cutoff

Reducing (1) using \(2^{t+1}\equiv-3\pmod{D_t}\) gives
\[
D_t\mid R,\qquad
R:=3\cdot2^{w-t}(2q+3)+2t-3.
\]
Here \(R>0\). Also
\[
2q+3=\frac{2y-2w+3}{D_w},
\qquad D_w>2^{w+1},
\]
and, since \(w\ge1\), \(0<2y-2w+3\le2y+1\). Therefore
\[
0<R<
\frac{3(2y+1)}{2^{t+1}}+2t-3. \tag{3}
\]

Suppose \(2^{2t}\ge2y\). Then (3) gives
\[
R<
3\cdot2^{t-1}+\frac{3}{2^{t+1}}+2t-3
<D_t.
\]
For the last strict inequality, the difference between \(D_t=2^{t+1}+3\) and the displayed upper bound is
\[
2^{t-1}+6-2t-\frac{3}{2^{t+1}}>0;
\]
indeed \(2^{t-1}\ge2t-2\) for every \(t\ge1\). This contradicts \(D_t\mid R\). Hence
\[
\boxed{t\le w\quad\Longrightarrow\quad 2^{2t}<2y.} \tag{4}
\]

Thus, when the second predecessor valuation does not exceed the first, it is at most half the binary logarithm of the final target, up to the displayed constant.

## Case \(t>w\): an exact dyadic-residue window

Because \(t\ge w+1\), reducing the second parent equation
\[
b=(2^{t+1}+3)q'+3\cdot2^t+t+3
\]
modulo \(2^{w+1}\), and using \(b\equiv2^w\pmod{2^{w+1}}\), gives
\[
3q'\equiv2^w-t-3\pmod{2^{w+1}}.
\]
Let
\[
\rho_{w,t}:=\operatorname{rem}_{2^{w+1}}(2^w-t-3)
\in\{0,\ldots,2^{w+1}-1\}.
\]
Since \(q'\ge0\), the congruence implies \(3q'\ge\rho_{w,t}\). On the other hand,
\[
q'<\frac{b}{2^{t+1}}<\frac{y}{2^{t+1}},
\]
because \(D_t>2^{t+1}\) and \(b<y\). Therefore
\[
\boxed{
t>w\quad\Longrightarrow\quad
\rho_{w,t}<\frac{3y}{2^{t+1}}.
} \tag{5}
\]

This residue window is valid even for small \(w\), where a crude estimate \(2^{w+t}<Cy\) need not hold. It says that a large \(t\) forces \(t\) into a narrow residue window modulo \(2^{w+1}\).

There is a useful dichotomy. If \(2^w\ge2(t+3)\), then \(2^w-t-3\) is already between \(2^{w-1}\) and \(2^w-1\), so it equals \(\rho_{w,t}\). Equation (5) then gives
\[
\boxed{2^{w+t}<3y.} \tag{6}
\]
Otherwise \(2^w<2(t+3)\). Since \(b\ge\beta_t>3\cdot2^t\) and \(b<y\), we have \(t<\log_2(y/3)\), and consequently
\[
\boxed{
w<\log_2\!\bigl(2\log_2(y/3)+6\bigr).
} \tag{7}
\]
So the only exception to the sum bound (6) has a first valuation logarithmic in \(\log y\), not of order \(\log y\).

The small-\(w\) exception is real and cannot simply be discarded. For example, take \(t=29,q'=0\). Then
\[
b=3\cdot2^{29}+32,\quad w=v_2(b)=5,\quad
q=25\,165\,823,\quad y=1\,686\,110\,245.
\]
Here \(t>w\), \(\rho_{5,29}=0\), and \(2^{w+t}>3y\). The residue-window statement (5) remains exact.

## Specialization to the cancellation family

For the second-level target in the existing sieve, let
\[
r=110j+50,\qquad
a=\frac{9^r+5}{2},\qquad A=2^a,
\]
and
\[
55y=8A P_r(A)+25,\qquad
P_r(A)=\sum_{i=0}^{2r-1}(-3)^iA^{2r-1-i}.
\]
The identity
\[
(A+3)P_r(A)=A^{2r}-9^r
\]
and \(A>3\) give \(0<P_r(A)<A^{2r-1}\). Hence
\[
0<y<A^{2r}=2^{2ra}. \tag{8}
\]

Combining (4)--(8), every two-step chain into this target through a first predecessor of valuation \(w\ge1\), followed by an even-predecessor valuation \(t\ge1\), must satisfy one of:

1. \(t\le w\), with \(t\le ra\);
2. \(t>w\) and \(2^w\ge2(t+3)\), with \(w+t\le2ra+1\);
3. \(t>w\) and \(2^w<2(t+3)\), with \(w<\log_2(4ra+6)\).

These are explicit restrictions on the even-predecessor branch. They complement, rather than repeat, the mod-\(25\)/mod-\(125\) odd-block partition in [Agent 20's second-level odd-block filter](../agent20-needle-coprime/SecondLevelOddBlockFilter.md). In particular, they apply to candidate parents whose source cannot have an odd predecessor, the large complementary branch identified there.

## What this does not establish

The congruence (2) and bounds (4)--(7) are necessary conditions on a two-edge synthetic ancestry. They do not prove that any candidate parent exists, do not decide the remaining \(t>w\) residue windows, do not establish genuine blank-root reachability or nonreachability, and do not determine BB(6).

The derivation is paper-level in this note. No Lean compile or axiom audit is claimed. The local shell and Python execution tools returned platform ClientError in this invocation, so CI was not used as a substitute for the required local preflight.


## Parallel bounds after a one-step odd block

There is a related bound for the one-step odd-entry subcase in Agent 20's mod-\(25\)/mod-\(125\) partition. Assume \(b\equiv1\pmod5\), so its unique odd predecessor is
\[
x=\frac{2b+3}{5}.
\]
Suppose this \(x\) has an immediate predecessor at valuation \(t\ge1\):
\[
x=D_tq'+\beta_t.
\]
The exact equation is
\[
2b+3=5D_tq'+15\cdot2^t+5t+15.
\]
As in the existing forced-even reduction, it implies
\[
D_t\mid4b+21-10t. \tag{9}
\]
Eliminating the first parent quotient gives the further necessary congruence
\[
\boxed{
D_t\mid
2^{w+1}(4y-4w+27-10t)+63-30t.
} \tag{10}
\]

If \(t\le w\), reduce (9) using \(2^{t+1}\equiv-3\pmod{D_t}\):
\[
D_t\mid R_{\rm odd},\qquad
R_{\rm odd}:=
3\cdot2^{w-t+1}(2q+3)+10t-21.
\]
This residue is positive for every \(t\ge1\). The same bound on \(2q+3\) used above gives
\[
0<R_{\rm odd}<
\frac{3(2y+1)}{2^t}+10t-21.
\]
If \(2^{2t}\ge8y\), the right side is strictly less than \(D_t\): indeed it is bounded above by
\[
3\cdot2^{t-2}+\frac{3}{2^t}+10t-21,
\]
whose difference from \(D_t\) is
\[
5\cdot2^{t-2}+24-10t-\frac{3}{2^t}>0
\]
(the inequality is immediate for \(t=1,2\), and for \(t\ge3\) use \(5\cdot2^{t-2}\ge10t-20\)). Therefore
\[
\boxed{t\le w\quad\Longrightarrow\quad 2^{2t}<8y.} \tag{11}
\]
For the actual cancellation family, (8) yields \(t\le ra+1\).

If \(t>w\), reducing the exact equation for \(x\) modulo \(2^{w+1}\) gives
\[
15q'\equiv-5t-12\pmod{2^{w+1}}.
\]
Let \(\sigma_{w,t}\) be the least nonnegative residue of
\[
-15^{-1}(5t+12)\pmod{2^{w+1}},
\]
where \(15^{-1}\) is the inverse modulo \(2^{w+1}\). Then \(q'\ge\sigma_{w,t}\). Since \(x=(2b+3)/5<y\) for \(y>1\), and \(q'<x/2^{t+1}\), we obtain the second dyadic window
\[
\boxed{\sigma_{w,t}<\frac{y}{2^{t+1}}.} \tag{12}
\]

This extension applies only to the one-step odd-block cases whose odd predecessor \(x\) then has an even predecessor. It does not dispose of the four mod-\(125\) families that can support longer odd blocks.
