# Two further high-stop exclusions inside the \(r\equiv2400\pmod{65536}\) residual

**Status:** exact paper-level source-parent compositions, not yet integrated into Lean or compiled. These close two infinite subfamilies of the explicit \(Y(n)\) residual isolated in [Root32HighStopR2400.md](./Root32HighStopR2400.md). They do not close the whole \(r\equiv2400\pmod{65536}\) class.

## 1. Starting residual and its complete source-parent reduction

The corrected R2400 analysis reduces the remaining high-stop possibility, for
\[
t=671+1024n,
\]
to reachability of
\[
Y(n)=
(2026954872744+3092060518680n,\;
 1351544872375+2061742269300n).
\]
Write
\[
Y_x+Y_y+1=4H(n),\qquad
H(n)=844624936280+1288450696995n.
\]

Suppose \(n\) is odd. Then \(H(n)\) is odd, so
\[
v_2(Y_x+Y_y+1)=2.
\]
Apply the complete original source grammar to a predecessor of \(Y(n)\). The target has even left coordinate, odd right coordinate, and odd coordinate sum. Thus the zero-left and even-\(a\) high branches (which require an even sum) and the low branch (which requires even right coordinate) are impossible. The \(a=1\) high branch requires \(16\mid Y_x+Y_y+1\), impossible at exact valuation two. In the remaining odd-\(a\) high branch, the cost equation forces the bounce depth \(d\) even, while \(2a+6\) is divisible by four, so \(d\le v_2(Y_x+Y_y+1)-2=0\). Hence \(d=0\) and the only possible source parent is
\[
A(m)=
(4266151266547+5153802787980m,\;
 3839719204110+4638643663290m),
\qquad n=2m+1.
\]
Its right coordinate is even and at least six. The even-right inverse theorem also requires the target sum not to be \(0\) or \(7\pmod8\). Here
\[
A_x+A_y=8105870470657+9792446451270m,
\]
which is \(3\pmod8\) when \(m=3\pmod4\) (the \(n=7\pmod8\) case) and \(5\pmod8\) when \(m=6\pmod8\) (the \(n=13\pmod{16}\) case). Thus both additional even-right side conditions hold. The exact even-right inverse therefore forces
\[
B(m)=
(8105870470655+9792446451270m,\;
 1919859602054+2319321831645m).
\]
Consequently, for odd \(n\), \(Y(n)\) is reachable only if \(B(m)\) is reachable.

## 2. First subfamily: \(n\equiv7\pmod8\)

Put \(n=7+8p\), so \(m=(n-1)/2=3+4p\). From the affine formula for \(B\),
\[
B_x\equiv3+2m\equiv1\pmod4,\qquad
B_y\equiv2+m\equiv1\pmod4.
\]
Thus \(B_y\) is odd and
\[
B_x+B_y\equiv2\pmod4.
\]
The source-certified blank_no_odd_sum_two theorem excludes \(B(m)\). Therefore \(Y(n)\), and hence the original high-stop target, is unreachable for every \(n\equiv7\pmod8\).

Here
\[
t=671+1024(7+8p)=7839+8192p.
\]
The exact root equation
\[
17300+22155(t+j)=5\cdot2^{E-17}
\]
has right side divisible by \(8192\). Since \(22155^{-1}\equiv291\pmod{8192}\), it gives
\[
t+j\equiv3780\pmod{8192},
\qquad j\equiv4133\pmod{8192}.
\]
With \(r=32+64j\), this is the infinite root-index progression
\[
\boxed{r\equiv264544\pmod{524288}.}
\]

## 3. Second subfamily: \(n\equiv13\pmod{16}\)

Put \(n=13+16p\), so \(m=6+8p\). The same affine parent \(B(m)\) satisfies
\[
B_x\equiv3\pmod4,\qquad B_y\equiv4\pmod8.
\]
In particular, \(B_y\equiv4\pmod8\) is even and at least six. The even-right inverse's sum side conditions also hold, since
\[
B_x+B_y=10025730072709+12111768282915m\equiv3\pmod8
\]
for \(m=6\pmod8\). If \(B(m)\) were reachable, the exact even-right inverse would force
\[
C(m)=\left(B_x+B_y-2,\frac{B_y-2}{2}\right).
\]
Because \(B_y\equiv4\pmod8\),
\[
C_y=\frac{B_y-2}{2}\equiv1\pmod4,
\]
so \(C_y\) is odd and at least five. Also
\[
C_x+C_y
=B_x+\frac{3B_y-6}{2}
\equiv3+3\equiv2\pmod4.
\]
The source-certified blank_no_odd_sum_two theorem excludes \(C(m)\). Therefore \(B(m)\), \(Y(n)\), and the high-stop target are unreachable for every \(n\equiv13\pmod{16}\).

Here
\[
t=671+1024(13+16p)=13983+16384p.
\]
Reducing the exact root equation modulo \(16384\), with
\(22155^{-1}\equiv8483\pmod{16384}\), gives
\[
t+j\equiv11972\pmod{16384},
\qquad j\equiv14373\pmod{16384}.
\]
Thus
\[
\boxed{r\equiv919904\pmod{1048576}.}
\]

## 4. Scope and residual

Both progressions lie inside the previously unresolved \(r\equiv2400\pmod{65536}\) class:
\[
264544\equiv919904\equiv2400\pmod{65536}.
\]
They are disjoint (their \(j\)-classes are \(4133\pmod{8192}\) and \(14373\pmod{16384}\)). They are also disjoint from all eight previously catalogued high-stop cylinders.

The result is a pair of new infinite high-stop exclusions obtained by continuing the exact Y(n) source-parent analysis, not a closure of the entire residual. The other odd-\(n\) residues and all even-\(n\) cases remain open. The derivation uses the existing complete source grammar, even-right unique inverse, and blank_no_odd_sum_two; it still needs a Lean wrapper, exact transitive source-closure compile, and axiom audit. Keep it in im-results/.
