# Three-state ternary Mealy transducer for the #623 drain

**Status.** This is an exact arithmetic transducer for the explicit normal-form integer used in the #623 drain analysis. Combined with the existing valuation normal form, it turns the drain's correction statistics into additive outputs of a three-state machine. The whole-drain source normal form is still a paper-level derivation with an uncompiled Lean draft; this note does not claim source-CI certification, blank-root nonhalting, or a value of BB(6).

## 1. Normal-form integer

For a positive drain block counter \(b\), let \(L\) be the unique integer satisfying
\[
L\equiv b\pmod 2,\qquad 3^{L-1}\le 2b-1<3^{L+1},
\]
and put
\[
N=\frac{2b-1+3^L}{4}.
\]
The parity condition makes \(N\) integral, and the inequalities give \(3^{L-1}\le N<3^L\). The existing valuation normal form identifies the base-three digits of \(N\) with the nonzero coefficients in the sparse expansion of the whole drain.

The result below gives a finite-state way to generate those digits directly from the low-to-high ternary digits of \(b\), without iterating the valuation descent.

## 2. The three-state transducer

Write
\[
d_i=\left\lfloor b/3^i\right\rfloor\bmod 3\in\{0,1,2\}.
\]
Read the digits \(d_0,d_1,\ldots,d_{L-1}\) from least significant to most significant.

The first digit has a special initial transition:

| Input \(d_0\) | Output \(n_0\) | Carry \(c_1\) |
|---:|---:|---:|
| 0 | 2 | 3 |
| 1 | 1 | 1 |
| 2 | 0 | -1 |

Thereafter the carry state is always in \(\{-1,1,3\}\). The transition table lists (output digit, next carry):

| Current carry \(c_i\) | Input \(d_i=0\) | Input \(d_i=1\) | Input \(d_i=2\) |
|---:|---:|---:|---:|
| -1 | (1, 1) | (0, -1) | (2, 1) |
| 1 | (2, 3) | (1, 1) | (0, -1) |
| 3 | (0, 1) | (2, 3) | (1, 1) |

Equivalently, for \(i\ge1\), \(n_i\) is the least residue of \(2d_i-c_i\) modulo 3, and
\[
c_{i+1}=\frac{4n_i+c_i-2d_i}{3}.
\]
The table proves closure of the three carry states and the digit identity
\[
4n_i+c_i=2d_i+3c_{i+1}.
\]
The initial transition satisfies
\[
4n_0=2d_0-1+3c_1.
\]

Define the transducer output
\[
N_T=\sum_{i=0}^{L-1}n_i3^i.
\]

### Exactness proof

For every \(j\in\{1,\ldots,L\}\), induction on \(j\) gives the telescoping identity
\[
4\sum_{i=0}^{j-1}n_i3^i
=
2\sum_{i=0}^{j-1}d_i3^i-1+c_j3^j.
\tag{1}
\]
The base case is the initial-transition identity. For the induction step, multiply the next digit identity by \(3^j\) and add it to (1).

Write \(b=b_{<L}+k3^L\), where \(b_{<L}=\sum_{i<L}d_i3^i\) and \(k=\lfloor b/3^L\rfloor\). At \(j=L\), (1) becomes
\[
4N_T=2b_{<L}-1+c_L3^L.
\tag{2}
\]
On the other hand, the normal-form integer satisfies
\[
4N=2b-1+3^L
=2b_{<L}-1+(2k+1)3^L.
\tag{3}
\]
Every output digit is in \(\{0,1,2\}\), so \(0\le N_T<3^L\); also \(0\le N<3^L\). Equations (2) and (3) imply that \(3^L\) divides \(N_T-N\), because \(4\) is invertible modulo \(3^L\). The two integers lie in the same interval of length \(3^L\), hence \(N_T=N\), and then \(c_L=2k+1\).

The defining upper bound on \(L\) implies \(b<2\cdot3^L\), so \(k\in\{0,1\}\). Thus the terminal carry is exactly:
- \(c_L=1\) when \(b<3^L\);
- \(c_L=3\) when \(3^L\le b<2\cdot3^L\).

In particular, the terminal carry records the one possible high digit of \(b\) above the \(L\) digits read by the transducer. The transducer output digits \(n_i\) are exactly the ordinary base-three digits of \(N\).

## 3. Additive correction outputs

Let \(z_0,z_1,z_2\) be the numbers of output digits equal to \(0,1,2\), respectively. Then
\[
z_0+z_1+z_2=L,\qquad
R=z_1+z_2,\qquad
D=L-2z_2.
\]
Here \(R\) is the **full** drain iteration count, i.e. the number of nonzero digits of \(N\). In the right-even sector the root-cocycle count \(r\) excludes the initial evaluator, so \(r=R-1\); in the other three sectors \(r=R\).

For the canonical correction pair \((\beta,\delta)\), put
\[
U=\beta+\delta,\qquad T=\delta-\beta.
\]
The exact sector formulas become the following weighted digit sums:

| Sector | Drain input \(b\) | \(U\) | \(T\) |
|---|---:|---:|---:|
| LO | \(q+3\) | \(z_0+3z_1+z_2+9\) | \(3z_0+5z_1-z_2+19\) |
| LE | \(q+2\) | \(z_0+3z_1+z_2+6\) | \(3z_0+5z_1-z_2+10\) |
| RO | \(q-1\) | \(z_0+3z_1+z_2+4\) | \(3z_0+5z_1-z_2-4\) |
| RE | \(q+1\) | \(z_0+3z_1+z_2+4\) | \(3z_0+5z_1-z_2+2\) |

Thus one transducer pass produces both exact correction statistics. The per-digit output weights are only
\[
u(0),u(1),u(2)=(1,3,1),\qquad
t(0),t(1),t(2)=(3,5,-1),
\]
with a sector-dependent constant.

### Direct interface to the existing integer carry transducer

The existing integer-coordinate maps use \(x=2g-\gamma_s\), \(y=6q\), with
\[
L:\ (x',y')=(x-3y+C_L,\ 3y+F_L),
\]
\[
R:\ (x',y')=(-4x-3y+C_R,\ 3x+3y+F_R).
\]
The following table rewrites their exact correction vectors as additive digit outputs. The right-even constants already account for \(r=R-1\).

| Sector | \(C_L\) | \(F_L\) | \(C_R\) | \(F_R\) |
|---|---|---|---|---|
| LO | \(-18z_0-34z_1+2z_2-122\) | \(12z_0+24z_1+84\) | \(12z_0+16z_1-8z_2-6\) | \(-6z_0-6z_1+6z_2+24\) |
| LE | \(-18z_0-34z_1+2z_2-68\) | \(12z_0+24z_1+48\) | \(12z_0+16z_1-8z_2-12\) | \(-6z_0-6z_1+6z_2+18\) |
| RO | \(-18z_0-34z_1+2z_2\) | \(12z_0+24z_1\) | \(12z_0+16z_1-8z_2-44\) | \(-6z_0-6z_1+6z_2+30\) |
| RE | \(-18z_0-34z_1+2z_2-36\) | \(12z_0+24z_1+18\) | \(12z_0+16z_1-8z_2-20\) | \(-6z_0-6z_1+6z_2+18\) |

This is the missing exact connection between the drain's low-to-high ternary carry and the additive corrections consumed by the two-coordinate carry transducer. It replaces an arbitrary correction rectangle by a source-determined weighted output, provided the normal-form-to-source-drain bridge is accepted.

## 4. Unified perturbed 3-Euclidean update

For a section state \(D(a,d)\), write
\[
S=a+d,\quad p=|a-d|,\quad q=\min(a,d),\quad g=p-3q.
\]
The exact source gap/scale equations give
\[
p'=|g-T|,\qquad S'=S+q+U,\qquad q'=(S'-p')/2.
\]
Indeed, if the exact output is left, then \(g\ge T\), \(p'=g-T\), and \(q'=3q+\delta\). If it is right, then \(g<T\), \(p'=T-g\), and \(q'=p+\beta\). In either case \(p'+2q'=S+q+\beta+\delta\).

This is an exact perturbed 3-Euclidean recurrence; it does not assume that output orientation is determined by the sign of \(g\). The new contribution here is that \(U,T\) are now explicit additive outputs of a three-state ternary transducer on the sector's drain input.

## 5. Reproduction and scope

Run **node verify_drain_digit_mealy.js 100000**.

The checker compares the transducer's output integer and terminal carry with the closed normal form, then independently compares \(D,R\) with the recursive valuation descent for every \(1\le b\le100{,}000\). The observed run had:
- zero discrepancies;
- maximum \(L=12\);
- terminal carry 1 in 77,857 cases and 3 in 22,143 cases;
- output digit counts \((z_0,z_1,z_2)=(328,827,\ 375,428,\ 312,897)\).

These checks are reproducibility diagnostics, not the proof. The transducer theorem is the finite carry table plus the telescoping induction above.

The source whole-drain normal form and its connection to the unchanged evaluator are described in [Agent41's valuation normal form](../agent41-623-3euclidean/DrainValuationNormalForm.md); the present transducer is a new finite-state realization of its integer \(N\), not a replacement proof of that source bridge. The existing two-coordinate carry machinery is in [Agent41's integer carry transducer](../agent41-623-integer-carry-transducer/README.md).

## 6. Next mathematical obligation

Compose this three-state drain transducer with the existing \(x,y\) digit/carry transducer. The resulting weighted product machine should compute the actual \((C_L,F_L,C_R,F_R)\) from the input digits of \(q+c_s\), rather than quantify over the full 55-case carry rectangle. Then seek a regular root-history language closed under the authentic \(D(0,7)\) transition. The finite synchronizing-word observations are not such a closure proof, and this note does not establish nonhalting of #623 or solve BB(6).
