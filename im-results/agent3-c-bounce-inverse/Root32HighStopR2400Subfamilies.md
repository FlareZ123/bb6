# One additional high-stop exclusion inside the \(r\equiv2400\pmod{65536}\) residual

**Correction:** only the \(n\equiv7\pmod8\) subfamily below is established. An earlier draft also claimed \(n\equiv13\pmod{16}\), but that argument applied the even-right inverse when its required sum-mod-8 side condition fails: the intermediate target has sum \(7\pmod8\). That second exclusion is withdrawn. The \(n\equiv13\pmod{16}\) root-index class is recorded as an unresolved target, not as a result.

## 1. Starting residual and its complete source-parent reduction for odd n

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
Apply the complete original source grammar to a predecessor of \(Y(n)\). The target has even left coordinate, odd right coordinate, and odd coordinate sum, with
\[
Y_y\ge1{,}351{,}544{,}872{,}375>7.
\]
Thus the zero-left and even-\(a\) high branches (which require an even sum) are impossible. The finite \(a=0\) case has right coordinate \(4\); the finite \(a=1\) cases have right coordinate \(1,3,5,\) or \(7\); and the \(a>1,k=0\) case has right coordinate \(2\). All are impossible because \(Y_y\) is enormous. The low branch requires even right coordinate and is impossible. In the \(a=1\) high branch, its \(y=3\) case is impossible, while the remaining case requires \(16\mid Y_x+Y_y+1\), impossible at exact valuation two. In the remaining odd-\(a\) high branch, the cost equation forces the bounce depth \(d\) even, while \(2a+6\) is divisible by four, so
\[
d\le v_2(Y_x+Y_y+1)-2=0.
\]
Hence \(d=0\) and the only possible source parent is
\[
A(m)=
(4266151266547+5153802787980m,\;
 3839719204110+4638643663290m),
\qquad n=2m+1.
\]
Its right coordinate is even and at least six. The even-right inverse theorem requires the target sum to be neither \(0\) nor \(7\pmod8\). Here
\[
A_x+A_y=8105870470657+9792446451270m.
\]
This is \(3\pmod8\) when \(m=3\pmod4\), and \(5\pmod8\) when \(m=6\pmod8\). Thus the additional even-right side conditions hold in both subfamilies considered below. The exact even-right inverse forces
\[
B(m)=
(8105870470655+9792446451270m,\;
 1919859602054+2319321831645m).
\]
Consequently, whenever \(m\equiv3\pmod4\) or \(m\equiv6\pmod8\) (the two subfamilies treated below), \(Y(n)\) is reachable only if \(B(m)\) is reachable. No such implication is asserted for the other odd-\(n\) residues, where the even-right side condition may fail.

## 2. Established subfamily: \(n\equiv7\pmod8\)

Put \(n=7+8p\), so \(m=(n-1)/2=3+4p\). From the affine formula for \(B\),
\[
B_x\equiv3+2m\equiv1\pmod4,\qquad
B_y\equiv2+m\equiv1\pmod4.
\]
Thus \(B_y\) is odd and
\[
B_y\ge1{,}919{,}859{,}602{,}054>5,
\qquad B_x+B_y\equiv2\pmod4.
\]
All hypotheses of the source-certified blank_no_odd_sum_two theorem hold, so it excludes \(B(m)\). Therefore \(Y(n)\), and hence the original high-stop target, is unreachable for every \(n\equiv7\pmod8\).

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

## 3. Unresolved attempted subfamily: \(n\equiv13\pmod{16}\)

Put \(n=13+16p\), so \(m=6+8p\). The same affine parent \(B(m)\) satisfies
\[
B_x\equiv3\pmod4,\qquad B_y\equiv4\pmod8,
\qquad B_x+B_y\equiv7\pmod8.
\]
The even-right inverse theorem cannot be applied to \(B(m)\), because its required \(hseven\) side condition fails.

The complete source grammar still gives a useful reduction. The low branch would force the parent
\[
C(m)=\left(B_x+B_y-2,\frac{B_y-2}{2}\right).
\]
Since \(B_y\equiv4\pmod8\), \(C_y=(B_y-2)/2\) is odd and at least \(7{,}917{,}895{,}295{,}961>5\); direct arithmetic gives \(C_x+C_y\equiv2\pmod4\). The source-certified blank_no_odd_sum_two theorem therefore excludes this low branch. The zero-left and even-\(a\) high branches require even target sum and are impossible. The finite \(a=0\) case has right coordinate \(4\); the finite \(a=1\) cases have right coordinate \(1,3,5,\) or \(7\); and the \(a>1,k=0\) case has right coordinate \(2\). These are all impossible because \(B_y\) is enormous. The remaining \(a=1\) high branch would require \(B_x+B_y+1\) to be a pure power of two, but
\[
B_x+B_y+1
=8Q(p),\qquad
Q(p)=10337042471275+12111768282915p,
\]
and \(Q(p)\) is divisible by five, so this branch is impossible as well.

Thus only the \(a>1\), odd-\(a\) high branch remains. Its cost equation forces the bounce depth \(d\) to be odd. The valuation of \(Q(p)\) is:
- \(v_2(Q)=0\) for \(p\equiv0,2\pmod4\), hence \(v_2(B_x+B_y+1)=3\) and \(d=1\);
- \(v_2(Q)=1\) for \(p\equiv1\pmod4\), hence \(v_2(B_x+B_y+1)=4\) and \(d=1\);
- \(v_2(Q)\ge2\) for \(p\equiv3\pmod4\), leaving odd depths \(d=1,3,\ldots\) up to the valuation bound.

This remaining odd-\(a\) high branch has not been excluded. Therefore no nonreachability result for the \(n\equiv13\pmod{16}\) family follows.

The parameter class translates to a root-index class, but it is **unresolved**:
\[
t=671+1024(13+16p)=13983+16384p.
\]
Modulo \(16384\), the exact root equation gives \(t+j\equiv11972\), hence \(j\equiv14373\pmod{16384}\) and \(r\equiv919904\pmod{1048576}\). This class is not part of the exclusion union.

## 4. Scope

The only new high-stop exclusion established by this note is
\[
\boxed{r\equiv264544\pmod{524288}.}
\]
The \(r\equiv919904\pmod{1048576}\) class remains open, as do the other odd-\(n\) residues and all even-\(n\) cases. This derivation is paper-level and still needs an integrated Lean wrapper, exact transitive source-closure compilation, and axiom audit. Keep it in im-results/.
