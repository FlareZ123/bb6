# Second-level odd-block history filter

**Status:** exact arithmetic reduction; intermediate research, not a BB(6) solution.  
**Date:** 2026-11-20.  
**Scope:** the second-level target in the family \(r=110j+50\), and its possible incoming parent valuations.

This note adds a root-history constraint to the second-level parent sieve. It also records the corrected eleven-prime CRT normalization: the base modulus \(900900\) already contains the prime \(13\), because one denominator cylinder is modulo \(39\).

## 1. Target and parent equation

Write
\[
r=110j+50,\qquad A=2^{a_r},\qquad a_r=(9^r+5)/2.
\]
Let \(P_r(A)\) be the polynomial sequence used in the cancellation construction. The second-level shifted target \(y\) satisfies
\[
55y=8A P_r(A)+25. \tag{1}
\]
For a possible parent of valuation \(w\), the exact inverse equation is
\[
y=D_wq+3\cdot2^w+w+3,\qquad D_w=2^{w+1}+3, \tag{2}
\]
with \(q\ge0\). Its shifted source counter is
\[
b=2^w(2q+3).
\]
A direct expansion of (2) gives the useful identity
\[
D_w(b-1)=2^w(2y+1-2w)-3. \tag{3}
\]
For reference, put \(N_w=2^w(2y+1-2w)-3\).

## 2. Exact congruence for the target modulo 25

We first establish
\[
\boxed{y\equiv 5+10j\pmod{25}.} \tag{4}
\]

Since \(r=110j+50\) is divisible by \(10\) and \(9^{10}\equiv1\pmod{200}\), we have
\[
9^r\equiv1\pmod{200},\qquad a_r\equiv3\pmod{100},
\]
hence \(A\equiv8\pmod{125}\).

The recurrence for \(P_n(A)\) is represented by the upper-right entry of
\[
T(A)^n,\qquad T(A)=
\begin{pmatrix}
A^2&A-3\\
0&9
\end{pmatrix}.
\]
Modulo \(125\), \(T(A)\) is therefore
\[
T=\begin{pmatrix}64&5\\0&9\end{pmatrix}.
\]
The finite matrix calculations are
\[
T^{50}\equiv
\begin{pmatrix}1&0\\0&1\end{pmatrix},
\qquad
T^{110}\equiv
\begin{pmatrix}101&75\\0&26\end{pmatrix}
\pmod{125}.
\]
If \(P_j\) denotes the upper-right entry of \(T^{110j}\), then
\[
P_0=0,\qquad P_{j+1}\equiv101P_j+75\cdot26^j\pmod{125}.
\]
As \(101\equiv1\) and \(26^j=(1+25)^j\equiv1+25j\pmod{125}\), this gives
\[
P_{j+1}\equiv P_j+75\pmod{125},\qquad
P_j\equiv75j\pmod{125}.
\]
Thus
\[
A P_r(A)\equiv8\cdot75j\equiv100j\pmod{125}.
\]
Using (1), dividing the resulting congruence by \(5\), and inverting \(11\) modulo \(25\), yields (4).

## 3. When can the parent source have an odd predecessor?

For \(w\ge1\), \(b\) is even. Such a source has an immediate odd predecessor exactly when
\[
b\equiv1\pmod5. \tag{5}
\]
Indeed, if \(b=5m+1\), then \(m\) is odd and the odd state with shifted counter \(2m+1\) maps in one odd step to the state with shifted counter \(5m+1=b\). Conversely, every positive odd block exits at a shifted counter congruent to \(1\) modulo \(5\).

Assume the parent equation (2), so \(D_w\mid N_w\). By (3), condition (5) is equivalent to
\[
5D_w\mid N_w.
\]

### Case \(w\not\equiv0\pmod4\)

Here \(D_w\) is invertible modulo \(5\), so (5) is equivalent to \(N_w\equiv0\pmod5\). Since \(y\equiv0\pmod5\), reducing \(N_w\) modulo \(5\) gives:

| \(w\bmod4\) | \(N_w\bmod5\) | Condition for \(b\equiv1\pmod5\) |
|---:|---:|---:|
| 1 | \(w-1\) | \(w\equiv1\pmod{20}\) |
| 2 | \(1-3w\) | \(w\equiv2\pmod{20}\) |
| 3 | \(-w\) | \(w\equiv15\pmod{20}\) |

### Case \(w\equiv0\pmod4\)

Now \(5\mid D_w\). Parent existence \(D_w\mid N_w\) first forces \(N_w\equiv0\pmod5\), hence \(w\equiv4\pmod5\), or
\[
w\equiv4\pmod{20}.
\]
For this class, \(D_w\equiv10\pmod{25}\), so \(v_5(D_w)=1\). Condition (5) therefore requires \(N_w\equiv0\pmod{25}\). Using \(2^w\equiv16\pmod{25}\) and (4),
\[
16(2y+1-2w)-3\equiv0\pmod{25}
\quad\Longleftrightarrow\quad
w\equiv y+9\pmod{25}.
\]
Combining \(w\equiv4\pmod{20}\) with \(w\equiv14+10j\pmod{25}\) gives
\[
w\equiv64-40j\pmod{100}.
\]

We have therefore proved the following exact necessary condition, conditional only on the parent equation (2):

\[
\boxed{
\begin{aligned}
b\equiv1\pmod5\quad\Longleftrightarrow\quad&
w\equiv1,2,15\pmod{20}\\
&\text{or }w\equiv64-40j\pmod{100}.
\end{aligned}}
\tag{6}
\]
The equivalence is conditional on (2); it does **not** guarantee that (2) has an integer solution \(q\). It only classifies the possible valuation residues of parents whose source has an odd predecessor.

Consequently, every actual parent valuation outside (6) lies on the even-predecessor branch: its source cannot have been entered by an odd step, so any genuine blank-root ancestry must enter that source from an even state.

## 4. Corrected eleven-prime CRT intersection

The denominator-cylinder base modulus is
\[
M_0=900900.
\]
It already contains \(13\), since the \(p=79\) cylinder uses \(w\equiv9\pmod{39}\). The \(p=13\) condition \(w\equiv12\pmod{13}\) on the cylinder \(w\equiv9\pmod{12}\) must therefore be applied directly to the base residue. It must **not** be counted as an additional independent factor of \(13\).

The correct full CRT modulus is
\[
L=900900\cdot19\cdot29\cdot37\cdot61\cdot67\cdot79\cdot101
=598939578493155900.
\]
The corrected eleven-prime sieve leaves, for every \(j\bmod33\),
\[
218715580637067540
\]
candidate valuation residues, of density
\[
\frac{4596796566563}{12588053352105}
\approx36.51713603\%.
\]

Intersecting those candidates with the odd-predecessor condition (6), over the combined \(j\)-period \(165=\operatorname{lcm}(33,5)\), leaves exactly
\[
24224993268961368
\]
residue classes modulo \(L\), for every \(j\bmod165\). This is
\[
\frac{25205067098}{623170958025}
\approx4.04464726\%
\]
of all valuation residues, and
\[
\frac{2545711776898}{22983982832815}
\approx11.07602540\%
\]
of the corrected eleven-prime survivors.

Thus **88.92397460% of the eleven-prime candidate residues are forced into the even-predecessor branch** if they are actual parents. These are residue-class counts, not counts of actual parents or reachable states.

The exact finite CRT calculation is reproducible with the companion script, second_level_eleven_prime_density.js. That script checks all \(j\bmod165\), and also checks the corrected total for all \(j\bmod33\).

## 5. Correction to the earlier CRT count

The previous eleven-prime script treated \(13\) as an extra CRT coordinate while \(13\) was already included in \(M_0\), and it did not impose the forced \(w\equiv12\pmod{13}\) condition on the base residue. Its reported modulus and survivor count are therefore not valid for the single integer valuation \(w\). The corrected modulus, count, density, and script are recorded above. The eight-prime and separate \(11^2\) calculations use bases that do not already contain \(13\), so this particular normalization error does not apply to those calculations.

## 6. Research significance and remaining gap

This is a root-history partition, not a nonhalting proof. It substantially narrows the possible odd-entry histories of the second-level target, but it does not decide whether any of the surviving candidate valuations actually satisfies the full parent equation. Nor does it resolve the even-predecessor branch.

The next mathematical target is to exploit the forced even predecessor for the large complementary set, rather than merely append more prime cylinders. The small odd-entry set should be followed through its explicit odd predecessor and tested for a further structural obstruction. A kernel-checked Lean formalization of (4), (3), and (6) remains desirable; this note is an arithmetic derivation, not a claim that the new lemmas have already been compiled in Lean.
