# Two-step even-predecessor bounds for the Space Needle cancellation target

**Status:** exact arithmetic necessary conditions with paper proofs, including a new all-parameter exclusion of the second-parent offset (t=w+1) throughout the wide cancellation band. This is an intermediate result, not a blank-root reachability theorem. No Lean compile or axiom audit is claimed.

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

## Offset-one second-parent exclusion across the wide band

The general two-step congruence has a stronger consequence at the adjacent valuation \(t=w+1\). This closes one entire second-parent offset throughout the large cancellation band, including the residue-cut exceptions \(c(s)<d\).

**Theorem.** Let \(r=110j+50\), \(n=3^{2r-1}\), \(d=1+\lfloor\log_2 n\rfloor\), and \(a=(9^r+5)/2\). Suppose
\[
(2r-1)s\ge a,\qquad (r-1)s\le a-d-3,\qquad s\ge1.
\]
For \(w=a+s-1\), the target \(y\) has no two-edge inverse chain whose first parent has valuation \(w\) and whose second parent has valuation \(w+1\).

**Proof.** If such a chain existed, the quotient-free congruence (2) would give
\[
D_{w+1}\mid 2^{w+2}(y+3-2w-1)+9-6(w+1).
\]
Since \(D_{w+1}=2^{w+2}+3\), reduction modulo \(D_{w+1}\) gives
\[
D_{w+1}\mid -3(y+1).
\]
As \(D_{w+1}\) is coprime to \(3\),
\[
D_{w+1}\mid y+1. \tag{15}
\]

Put \(u=2^{s+1}\) and \(S_u=\sum_{i=0}^{2r-1}u^i\). Then
\[
D_{w+1}=2^{a+s+1}+3=2^a u+3,
\qquad 2^a u\equiv-3\pmod{D_{w+1}}.
\]
The polynomial expansion of \(AP_r(A)\) used above therefore gives
\[
u^{2r}AP_r(A)\equiv 3^{2r}S_u=3nS_u\pmod{D_{w+1}}.
\]
Multiplying (15) by \(55u^{2r}\), using \(55(y+1)=8AP_r(A)+80\), and cancelling the factor \(8\) (the divisor is odd), yields
\[
D_{w+1}\mid Z,\qquad Z:=3nS_u+10u^{2r}.
\]
Write \(Z=D_{w+1}z\), with \(z\in\mathbb N_{>0}\).

We now choose a power-of-two cut adapted to the geometric sum. Set \(T=s+1\) and \(m_0=a+s-1\). Write \(m_0=L_0T+c_0\) with \(1\le c_0\le T\), taking \(c_0=T\) when \(T\mid m_0\). If \(c_0\ge d+1\), take \(m=m_0\), \(L=L_0\), \(c=c_0\). Otherwise take \(m=m_0-c_0=L_0T\), \(L=L_0-1\), \(c=T\). In either case,
\[
m=LT+c,\qquad c\ge d+1,\qquad m_0-d\le m\le m_0.
\]
Let \(M=2^m=u^L2^c\). The first band inequality implies
\[
2r(s+1)\ge a+s-1\ge m,
\]
so \(M\mid u^{2r}\). Also \(D_{w+1}\equiv3\pmod M\). Reducing \(Z=D_{w+1}z\) modulo \(M\) gives
\[
M\mid z-nS_u.
\]
Since \(c\le T\), \(M\mid u^{L+1}\); hence, with \(R=\sum_{i=0}^{L}u^i\),
\[
M\mid z-nR. \tag{16}
\]

For completeness, the size bounds are uniform over the whole stated band. First, \(9^r\ge16r^2\) for \(r\ge2\), so \(a\ge8r^2\) and the lower band bound gives \(s\ge4r\). Also
\[
3r-1\le d\le4r-2.
\]
Thus \(s\ge d+1\), and
\[
nR<2nu^L<M
\]
because \(R<2u^L\) and \(2^c\ge2^{d+1}>2n\).

Next, \(D_{w+1}>2^{a+s+1}\) and \(S_u<2u^{2r-1}\), so
\[
z<
6n\,2^{(2r-2)(s+1)-a}
+10\,2^{(2r-1)s+2r-1-a}.
\]
Using \(n<2^d\), \(m\ge a+s-1-d\), and the upper band inequality \((2r-2)s\le2a-2d-6\), the ratios of these two terms to \(M\) are respectively bounded above by
\[
6\cdot2^{\,2r-7-s}
\quad\text{and}\quad
10\cdot2^{\,2r-d-6}.
\]
The first is less than \(1/2\) because \(s\ge4r\); the second is less than \(1/2\) because \(d\ge3r-1\) and \(r\ge50\). Consequently \(0<z<M\).

Together with \(0<nR<M\), (16) forces \(z=nR\). But then \(Z=D_{w+1}z\) would be divisible by \(n\), whereas
\[
Z=3nS_u+10u^{2r}\equiv10u^{2r}\not\equiv0\pmod n,
\]
since \(n=3^{2r-1}\) and \(\gcd(10u,n)=1\). This contradiction proves the theorem. \(\square\)

The exclusion does not require \(c(s)\ge d\): it applies to every \(s\) in the two-inequality band, including all residue-cut exceptions. It removes only the adjacent second-parent valuation \(t=w+1\); all other second-parent valuations and authentic blank-root reachability remain open. The argument is paper-level and has not been Lean-compiled.

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


## Exact low-valuation slice: the \(t=1\) predecessor

The general two-step congruence also gives a concrete target-specific filter for an immediate predecessor of valuation \(t=1\). Here \(D_1=7\), and the second parent exists exactly when \(b\ge10\) and
\[
b\equiv3\pmod7.
\]
The target family has
\[
y\equiv
\begin{cases}
1\pmod7,&j\equiv0\pmod3,\\
5\pmod7,&j\equiv1\pmod3,\\
3\pmod7,&j\equiv2\pmod3.
\end{cases}
\]
Reducing (2) modulo \(7\) gives the following necessary classes for \(w\) modulo \(21\):
\[
\begin{array}{c|c}
j\bmod3 & w\bmod21\\ \hline
0&8,9,13\\
1&5,6,10\\
2&1,17,18
\end{array}
\]
The third class in each row is precisely the first-level \(p=7\) denominator cylinder \(w\equiv1\pmod3\); the other two classes have \(7\nmid D_w\) and lift to the exact \(w\bmod42\) classes
\[
\begin{array}{c|c}
j\bmod3 & w\bmod42\\ \hline
0&8,9,29,30\\
1&5,6,26,27\\
2&17,18,38,39.
\end{array} \tag{13}
\]

The denominator cylinder needs a \(49\)-lift because \(7\mid D_w\). For completeness, the target residue modulo \(49\) has period \(21\) in \(j\). Indeed \(9^{110j+50}\pmod{42}\) cycles as \(39,9,15\), so \(a\bmod21\) cycles as \(1,7,10\), and \(A\bmod49\) cycles as \(2,30,44\). For
\[
T(A)=\begin{pmatrix}A^2&A-3\\0&9\end{pmatrix},
\]
one checks \(T(2)^{2310}=T(30)^{2310}=T(44)^{2310}=I\pmod{49}\). The resulting \(y\bmod49\) values for \(j=0,\ldots,20\) are
\[
(8,5,45,43,26,45,29,47,45,15,19,45,1,40,45,36,12,45,22,33,45).
\]

The first-level \(p=7\) cylinder fixes \(w\bmod21\) to \(13,10,1\) according as \(j\bmod3\) is \(0,1,2\). Testing its seven lifts \(w=w_0+21k\pmod{147}\), \(0\le k<7\), against the parent equation modulo \(49\) and then \(b\equiv3\pmod7\), leaves exactly
\[
\boxed{
(j\bmod21,w\bmod147)\in
\{(9,13),(13,10),(15,34),(16,31)\}.
} \tag{14}
\]
For these classes the lift gives \(q\equiv1\pmod7\), so \(b\ge10\); thus the \(t=1\) parent condition is attained whenever the first-level parent itself exists. Equations (13)--(14) are a complete \(t=1\) residue filter, but they do not eliminate all such parents.


## Exact low-valuation slice: the \(t=1\) predecessor

The general two-step congruence also gives a concrete target-specific filter for an immediate predecessor of valuation \(t=1\). Here \(D_1=7\), and the second parent exists exactly when \(b\ge10\) and
\[
b\equiv3\pmod7.
\]
The target family has
\[
y\equiv
\begin{cases}
1\pmod7,&j\equiv0\pmod3,\\
5\pmod7,&j\equiv1\pmod3,\\
3\pmod7,&j\equiv2\pmod3.
\end{cases}
\]
Reducing (2) modulo \(7\) gives the following necessary classes for \(w\) modulo \(21\):
\[
\begin{array}{c|c}
j\bmod3 & w\bmod21\\ \hline
0&8,9,13\\
1&5,6,10\\
2&1,17,18
\end{array}
\]
The third class in each row is precisely the first-level \(p=7\) denominator cylinder \(w\equiv1\pmod3\); the other two classes have \(7\nmid D_w\) and lift to the exact \(w\bmod42\) classes
\[
\begin{array}{c|c}
j\bmod3 & w\bmod42\\ \hline
0&8,9,29,30\\
1&5,6,26,27\\
2&17,18,38,39.
\end{array} \tag{13}
\]

The denominator cylinder needs a \(49\)-lift because \(7\mid D_w\). For completeness, the target residue modulo \(49\) has period \(21\) in \(j\). Indeed \(9^{110j+50}\pmod{42}\) cycles as \(39,9,15\), so \(a\bmod21\) cycles as \(1,7,10\), and \(A\bmod49\) cycles as \(2,30,44\). For
\[
T(A)=\begin{pmatrix}A^2&A-3\\0&9\end{pmatrix},
\]
one checks \(T(2)^{2310}=T(30)^{2310}=T(44)^{2310}=I\pmod{49}\). The resulting \(y\bmod49\) values for \(j=0,\ldots,20\) are
\[
(8,5,45,43,26,45,29,47,45,15,19,45,1,40,45,36,12,45,22,33,45).
\]

The first-level \(p=7\) cylinder fixes \(w\bmod21\) to \(13,10,1\) according as \(j\bmod3\) is \(0,1,2\). Testing its seven lifts \(w=w_0+21k\pmod{147}\), \(0\le k<7\), against the parent equation modulo \(49\) and then \(b\equiv3\pmod7\), leaves exactly
\[
\boxed{
(j\bmod21,w\bmod147)\in
\{(9,13),(13,10),(15,34),(16,31)\}.
} \tag{14}
\]
For these classes the lift gives \(q\equiv1\pmod7\), so \(b\ge10\); thus the \(t=1\) parent condition is attained whenever the first-level parent itself exists. Equations (13)--(14) are a complete \(t=1\) residue filter, but they do not eliminate all such parents.


## Fixed-\(t\) prime projection

The quotient-free congruence (2) can be projected through any prime \(p\mid D_t\). Let \(m=\operatorname{ord}_p(2)\) and \(s=w\bmod m\). Since \(p\) is odd, (2) forces
\[
\boxed{
w\equiv y+3-t+(9-6t)\,2^{-(s+2)}\pmod p.
} \tag{15}
\]
Thus for each \(s\bmod m\), there is at most one residue \(w\bmod p\), giving at most \(m\) classes modulo \(pm\). When \(p\nmid D_w\), this is the exact \(p\)-component of the second-parent divisibility; when \(p\mid D_w\), it remains necessary but a higher \(p\)-adic lift may be needed. This is a reusable fixed-valuation sieve.

Three small examples for the cancellation family:

**Valuation \(t=2\), prime \(p=11\).** The target equation gives
\[
y\equiv2-j\pmod{11}.
\]
For example, \(9^{110j+50}\equiv1\pmod{220}\), hence \(a\equiv3\pmod{110}\) and \(A\equiv8\pmod{121}\). With
\[
T(8)=\begin{pmatrix}64&5\\0&9\end{pmatrix},
\quad T(8)^{50}=\begin{pmatrix}78&7\\0&1\end{pmatrix},
\quad T(8)^{110}=\begin{pmatrix}1&88\\0&1\end{pmatrix}
\pmod{121},
\]
one gets \(P_r(A)\equiv7+88j\pmod{121}\), and then \(5y\equiv10+6j\pmod{11}\). Formula (15), with \(s=w\bmod10\), becomes
\[
w\equiv\alpha_s-j\pmod{11},\qquad
(\alpha_0,\ldots,\alpha_9)=(5,4,9,6,10,1,2,8,0,7). \tag{16}
\]
The \(s=2\) class is the first-level \(p=11\) denominator cylinder; for the other nine values of \(s\), \(11\nmid D_w\), so (16) is the exact \(11\)-component of the \(t=2\) parent condition.

**Valuation \(t=3\), prime \(p=19\).** Here \(a\equiv7\pmod{18}\), \(A\equiv14\pmod{19}\), and direct matrix reduction gives \(y\bmod19\), periodic in \(j\bmod9\), as
\[
(12,4,16,10,17,16,7,8,16).
\]
For \(s=w\bmod18\), the necessary classes are
\[
w\equiv y_j-9\cdot2^{-(s+2)}\pmod{19}. \tag{17}
\]
The exceptional denominator cylinder is \(s=3\), where \(19\mid D_w\).

**Valuation \(t=4\), prime \(p=5\).** Since \(y\equiv0\pmod5\), (2) reduces to
\[
2^{w+2}(-w-1)\equiv0\pmod5,
\]
so every \(t=4\) second parent necessarily satisfies the particularly simple condition
\[
\boxed{w\equiv4\pmod5.} \tag{18}
\]
This applies whether or not \(5\mid D_w\); in the latter case it is only the first \(5\)-adic layer.


## Low-\(t\) filters intersected with the existing 11-prime first-parent sieve

I applied the \(t=1,2,3,4\) conditions above to the exact finite residue count in Agent 20's second_level_eleven_prime_density.js, rather than treating the new filters in isolation. The base modulus is \(900900\), the existing \(j\)-period is \(33\), and the seven additional prime cylinders are \(19,29,37,61,67,79,101\). The existing sieve's total is reproduced exactly: \(218715580637067540\) candidate residue classes per \(j\bmod33\), or
\[
B=7\,217\,614\,161\,023\,228\,820
\]
over the 33 \(j\)-classes.

The counts below are weighted counts of first-parent sieve residue classes, not counts of actual reachable machines. A "resolved" count means the full \(D_t\)-divisibility is determined because \(\gcd(D_t,D_w)=1\); a denominator-cylinder contribution is left unresolved because \(D_t\) and \(D_w\) share a prime and the first-parent sieve has not supplied the necessary higher lift.

| Second valuation | Resolved residue count | Unresolved shared-prime contribution | Share of first-parent candidates |
|---|---:|---:|---:|
| \(t=1\) | \(46\,696\,903\,278\,675\,056\,550\) | \(0\) after the \(49\)-lift | **13.203781% exactly** |
| \(t=2\) | \(651\,242\,185\,016\,565\,285\) | \(53\,950\,125\,841\,010\,685\) (\(p=11\)) | 9.022956% resolved; at most 9.770435% including cylinder |
| \(t=3\) | \(378\,352\,095\,619\,329\,480\) | \(28\,924\,344\,255\,968\,700\) (\(p=19\)) | 5.242065% resolved; at most 5.642812% including cylinder |
| \(t=4\) | \(208\,465\,420\,664\,370\,870\) | \(90\,544\,934\,470\,213\,080\) (\(p=5\)); \(125\,916\,061\,965\,066\,945\) (\(p=7\)); \(47\,059\,538\,310\,176\,535\) (both) | 2.888287% resolved; at most 6.539362% including cylinders |

For \(t=1\), the denominator is extended by \(7\) to account for the \(p=7\) lift; the corresponding first-level candidate denominator is \(49B\). The cylinder calculation uses the fact that among the seven \(j\bmod231\) lifts of a fixed \(j\bmod33\), exactly two are compatible with the surviving special \(j\bmod21\) classes when \(j\bmod3\in\{0,1\}\), and none when \(j\bmod3=2\).

For \(t=2\), the resolved count excludes \(w\equiv2\pmod{10}\), the shared \(p=11\) cylinder. For \(t=3\), it excludes \(w\equiv3\pmod{18}\), the shared \(p=19\) cylinder; outside it, the second-parent condition fixes one of the 19 free residues. For \(t=4\), the resolved count excludes both \(w\equiv0\pmod4\) and \(w\equiv1\pmod3\), the shared \(p=5\) and \(p=7\) cylinders.

The exact counting implementation is [low_t_parent_density.js](low_t_parent_density.js). It asserts agreement with Agent 20's published first-level count before producing the low-\(t\) splits. These results quantify the low-valuation branches only; they do not bound or eliminate \(t\ge5\), and they do not prove that any first-parent residue candidate is a genuine blank-root ancestor.


### Valuations \(t=5\) and \(t=6\)

The same weighted count extends one step further.

For \(t=5\), \(D_5=67\). The target recurrence gives \(y\bmod67=(29,20,22)\) for \(j\bmod3=0,1,2\), and (15) becomes, with \(s=w\bmod66\),
\[
w\equiv y_j-2-21\cdot2^{-(s+2)}\pmod{67}.
\]
The denominator cylinder is \(s=5\). Its first-level forced residue is \(w\equiv y_j-32\pmod{67}\), which agrees with the \(t=5\) projection; the higher lift remains unresolved. Outside this cylinder the \(t=5\) condition fixes one of the 67 free residues. The exact weighted count is \(107\,665\,434\,405\,024\,210\) resolved candidates (1.491703% of \(B\)); the unresolved cylinder contributes \(4\,030\,055\,886\,606\,750\), giving an upper bound of 1.547540%.

For \(t=6\), \(D_6=131\), \(\operatorname{ord}_{131}(2)=130\), and the denominator cylinder is
\[
w\equiv6\pmod{130},
\]
since \(2^7\equiv-3\pmod{131}\). Extend the first-level sieve by the new prime \(131\): outside this cylinder, the first-parent equation leaves 131 choices for \(w\bmod131\); inside it, the first-parent equation forces one. The \(t=6\) projection (15) fixes one of the 131 choices outside the cylinder, so the resolved count is \(7\,170\,304\,969\,989\,921\,375\). The cylinder contributes \(47\,309\,191\,033\,307\,445\) unresolved candidates. Relative to the extended first-level candidate count \(939\,357\,260\,259\,713\,007\,570\), this is 0.763320% resolved and at most 0.768356% including the cylinder.

These are again weighted residue-class counts. The \(t=6\) cylinder needs a \(131\)-adic lift; the result is not a branch closure.


### Valuation \(t=7\)

Here \(D_7=259=7\cdot37\). The \(p=7\) projection is
\[
2^{w+2}(y_j-w-4)\equiv33\pmod7.
\]
Outside the first-level \(p=7\) denominator cylinder \(w\equiv1\pmod3\), this is exact at \(p=7\). The \(p=37\) projection fixes one of the 37 free residues when \(w\not\equiv7\pmod{36}\). On the \(p=37\) denominator cylinder, the first-level forced residue is \(w\equiv y-17\pmod{37}\), exactly the \(t=7\) projected residue; also \(w\equiv7\pmod{36}\) implies \(w\equiv1\pmod3\), so this cylinder lies inside the unresolved \(p=7\) cylinder.

Intersecting with the same first-level sieve gives \(26\,769\,889\,212\,928\,290\) resolved candidates (0.370896% of \(B\)), all outside the shared \(p=7\) cylinder. The unresolved \(p=7\)-cylinder contribution is \(18\,941\,959\,298\,420\,730\), giving an upper bound of 0.633337%. The count is weighted residue classes, not a reachability result.
