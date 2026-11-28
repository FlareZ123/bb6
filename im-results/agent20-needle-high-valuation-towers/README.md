# Two further Space Needle all-depth valuation towers: 32,771-adic w=14 and 262,147-adic w=17

**Agent 20, 28 November 2026 UTC.** New elementary **all-depth prepared-high-level** arithmetic theorems. These extend the 3/5/6/11 deep branches of the source-accepted Space Needle cancellation family and yield two new independent deep arms. The existence/lifting proofs here are paper-level (inductive mathematics, exact integer regressions), **not yet Lean-certified**. The generic necessary congruence for *all* w≥2 is original-source-kernel accepted in [CI 46085435892](https://github.com/FlareZ123/bb6/actions/runs/46085435892). No authentic blank-tape root reachability or BB(6) decision is claimed.

## Common setup

Let \(a_r=(9^r+5)/2\), \(A_r=2^{a_r}\), and the source-identified prepared cancellation feeder counter
\[
B_r=2^{a_r-1}(A_r-3)\sum_{i=0}^{r-1}A_r^{2(r-1-i)}9^i,\qquad
2(A_r+3)B_r=A_r(A_r^{2r}-9^r).
\]
The exact valuation-w original high-level predecessor relation for shifted targets B is
\[
B=(2^{w+1}+3)q+(3\cdot2^w+w+3),\quad q\ge0,\quad
\operatorname{parent}=2^w(2q+3).
\]
Thus when \(p=2^{w+1}+3\) is prime, **k rational valuation-w inverse steps are integral iff**
\[
p^k\mid 3B+2^w(2w-3).\tag{1}
\]
For sufficiently large B in this congruence class, all steps are genuine nonnegative-source high-level transitions, because the inverse affine map is increasing in B, its unique fixed point is negative, and the original cancellation feeder B_r grows superexponentially with r.

## Theorems and explicit constants

Fix the Agent47 original-source five-parent index class
\[
R=4152608179,\quad Q=35697042810,\quad r\equiv R\pmod Q.
\]
There are **two more** one-step valuation families within this class, each lifting to arbitrary inverse depth. The data are:

| valuation w | prime p=2^(w+1)+3 | base index r0 | base period S | constant derivative δ mod p |
|---:|---:|---:|---:|---:|
| 14 | 32771 | 279297815553619 = R+7824Q | 3275417860074360 = 91756Q | 14966 |
| 17 | 262147 | 106238552010739 = R+2976Q | 6814064964191760990 = 190885979Q | 227076 |

**Theorem (two new all-depth branches).** For either row, every k≥1 and every r≡r0 modS,
\[
\boxed{B_{r+S\,p^{k-1}}-B_r\equiv\delta\,p^k\pmod{p^{k+1}}.}\tag{2}
\]
Both slopes are units: \(0<14966<32771\), \(0<227076<262147\), and both p are primes. Also \(B_{r_0}\equiv3\cdot2^w+w+3\pmod p\). Therefore for each k there exists **exactly one lifted residue**
\(r_{w,k}\pmod{S\,p^{k-1}}\) extending r0 modS that satisfies (1). In that residue class, all sufficiently large r have k genuine prepared incoming high-level steps of constant valuation w before the cancellation terminal edge. These are **infinitely many per k**, not a single very large finite ancestry scan.

Initial lifted classes:

| w | k=2 representative | k=2 period | k=3 representative |
|---:|---:|---:|---:|
| 14 | 77745597624540562579 | 107338718692496851560 | 3442001099191228582685539 |
| 17 | 559387035211632786962809 | 1786286688167977568245530 | 291901239673940762014925511169 |

The final [joint six-arm theorem](../agent20-needle-joint-towers/SIX-DEEP-ARMS.md) shows both towers are compatible with the preexisting 3/5/6/11 ones simultaneously, giving six depth-k branches inside one feeder.

## Proof of uniform derivative (2)

The argument works for both parameter rows, using only finite residue certificates, elementary exponent laws, and the binomial lifting identity
\[
(1+pc)^{p^{k-1}}\equiv1+cp^k\pmod{p^{k+1}}
\quad(k\ge1,\ p\text{ odd prime}).\tag{3}
\]

Let E=ord_p(2), N=ord_p(9). The row-specific **exact small-period certificates** are:

| w | E | N | residual modulus for 9^r in \(2E\) | period \(T_a\) | S/E and S/N integral? |
|---:|---:|---:|---:|---:|---|
| 14 | 32770 | 3277 | 65540 | 56 | yes |
| 17 | 262146 | 43691 | 174764=2E/3 | 21845 | yes |

For w14, \(9^{56}\equiv1\pmod{65540}\), and 9 is a unit modulo65540. For w17, \(9^{21845}\equiv1\pmod{174764}\); the missing factor3 in \(2E=524292\) is already supplied by \(9^r\), since r≥1. The base shift S is divisible by E,N and \(T_a\). Consequently
\[
a_{r+S}-a_r\equiv0\pmod E,\quad
2^{a_{r+S}}\equiv2^{a_r}\pmod p
\]
and the exact polynomial B_r modp is constant along the class r≡r0 modS (also r modE and r modN are constant). At the selected bases, exact modular evaluation from the polynomial gives
\[
B_{r_0}\bmod p=\begin{cases}
16398,& w=14,\\
131089,& w=17,
\end{cases}
\]
exactly \(3\cdot2^w+w+3\bmod p\).

For any k≥1 put t=S p^(k−1). Fermat/binomial lifting gives \(9^t\equiv1\pmod{p^k}\). The same residual-period argument makes \(a_{r+t}-a_r\) divisible by E, and its explicit formula
\[
a_{r+t}-a_r=9^r(9^t-1)/2
\]
also makes it divisible p^k, hence E p^k because gcd(E,p)=1. Therefore
\[
A_{r+t}\equiv A_r\pmod{p^{k+1}}.
\tag{4}
\]
Define the finite computable coefficients
\[
q_2=\frac{2^E-1}p\bmod p,\quad q_9=\frac{9^N-1}p\bmod p,\quad
\alpha=2(S/E)q_2\bmod p,\quad
\beta=(S/N)q_9\bmod p.
\]
Then
\[
A_r^{2t}\equiv1+\alpha a_r p^k,\quad
9^t\equiv1+\beta p^k\pmod{p^{k+1}}.
\tag{5}
\]
On the selected index class, \(A_r+3\not\equiv0\pmod p\), so \(2(A_r+3)\) is a modular unit. Subtract the exact polynomial identity at r+t and r and substitute (4)-(5):
\[
B_{r+t}-B_r\equiv p^k\frac{A_r}{2(A_r+3)}
(\alpha a_r A_r^{2r}-\beta9^r)\pmod{p^{k+1}}.\tag{6}
\]
The coefficient depends only on the fixed base index class r≡r0 modS. All the required finite source-independent modular values are:

| w | q2 | q9 | α | β | a_r modp | A_r modp | A/(2(A+3)) modp | A^(2r) modp | 9^r modp |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 14 | 24180 | 31030 | 11597 | 17015 | 17567 | 31431 | 1128 | 22070 | 2358 |
| 17 | 90594 | 223162 | 227468 | 255899 | 178617 | 28353 | 125014 | 219266 | 95082 |

Inserting these into (6) gives precisely \(14966\pmod{32771}\) and \(227076\pmod{262147}\), proving (2) for every k. All finite modular residues can be checked using ordinary repeated-square arithmetic and primality of 32771 and262147 by trial division up to their square roots; the listed exact [audit](w14_w17_audit.py) independently recomputes them.

## Hensel induction, source legality, and limitations

Let the unique fixed-point target \(C_{w,k}\equiv-(2^w(2w-3))3^{-1}\pmod{p^k}\). On the base r0 class, \(B_r=C_{w,1}\pmod p\). Suppose the unique residue r_(w,k) achieves depth k. Its p possible lifts r_(w,k)+jS p^(k−1) (j=0,...,p−1) keep the old condition and, by (2), have new p-adic digits that advance by jδ. Since gcd(δ,p)=1, exactly one equals C_(w,k+1). This constructs one and only one residue class at every depth. As \(B_r\ge2^{9^r+3}\to\infty\), choose r sufficiently large in each class to keep all k affine reverse targets above the legal \(3\cdot2^w+w+3\) threshold. The exact high-level source is then \(2^w(2q+3)\), of valuation w.

The proof's sole limitation is **root**: there is no evidence that any of these prepared feeders is reached from the unique blank-tape Space Needle configuration. This work does not discharge its Raw10 weighted Cover, any Canonical40 member, or an exact BB(6) maximality theorem.
