# Exact second parent fan for the Machine C low-stop family

**Status:** exact paper-level classification derived from the repository's complete original-section inverse predicate. This is not yet a Lean-compiled theorem and is not a blank-root exclusion by itself.

## Setup

Restrict the first low stopping family to
\[
m=512z+67,\qquad z\ge0.
\]
This is the subfamily \(m=64u+3\) with \(u=8z+1\). Put
\[
w=2^{2m-1}-(96z+13).
\]
The exact predecessor calculations in [the main dossier](README.md) force the chain
\[
(1,K_m)\leftarrow(8w,12w)\leftarrow(20w-2,6w-1)
\leftarrow(13w-4,(19w-7)/2)\leftarrow R_z,
\]
where
\[
R_z=(x,y)=((45w-23)/4,(83w-49)/8).
\]
The preceding odd/odd state has only the depth-zero even-left parent because
\(v_2(9u+1)=1\). Thus \(R_z\) is the first state whose complete parent fan needs further analysis.

## Exact affine valuation

Let
\[
F(z)=519z+73,\qquad d=v_2(F(z)),\qquad F(z)=2^d q
\]
with \(q\) odd. Direct simplification gives
\[
x+y+1=\frac{173w-87}{8}
=173\,2^{2m-4}-4F(z).
\]

The following elementary bounds make the valuation exact. Since
\(m=512z+67\),
\[
F(z)=519z+73<1024(z+1)\le2^{z+11}\le2^{2m-6}.
\]
Hence \(d<2m-6\). Therefore
\[
x+y+1
=2^{d+2}\underbrace{\left(173\,2^{2m-d-6}-q\right)}_{H}.
\]
The exponent \(2m-d-6\) is positive, so the first term in \(H\) is even and \(q\) is odd. Also \(q<2^{2m-d-6}\), so
\[
H>172\,2^{2m-d-6}\ge344.
\]
Consequently \(H\) is odd and strictly greater than one. In particular,
\[
v_2(x+y+1)=d+2,
\]
and \(x+y+1\) is **not** a pure power of two.

We also have \(w>m\), hence \(x>5\) and
\[
y=\frac{83w-49}{8}>6m+2.
\]
For the last inequality, \(83m-49>48m+16\) for \(m\ge2\).

## Complete source-parent classification of \(R_z\)

Apply the exact theorem BB6.Agent46.complete_section_inverse to the target \((x,y)\), with \(x\) even and \(y\) odd.

- The \(a=0\) branch requires \(x+y=8\cdot2^n\), impossible because \(x+y\) is odd.
- The exceptional \(a=1\) outputs are \((2,5)\) and \((0,7)\), excluded by \(x>5\). Its general branch requires \(x+y+1=16\cdot2^n\), impossible because the odd factor \(H\) above is greater than one.
- The direct branch requires \(y=2k+2\), impossible because \(y\) is odd.
- The even-\(a\ge2\) bounce branch requires \(x+y\) even, also impossible.
- Thus every source parent is in the odd-\(a\ge3\) bounce branch.

For that branch, the complete inverse predicate gives
\[
x+y+1=2^{n+1}(a+3),\qquad
2k+a+7+3n=x+2y.
\]
Since \(a+3\) is even and \(v_2(x+y+1)=d+2\), necessarily \(n\le d\). The second equation has even right-hand side, while \(a+7\) is even, so \(n\) must be even.

Conversely, every even \(n\le d\) gives a genuine source parent. Define
\[
a_n=\frac{x+y+1}{2^{n+1}}-3
=2^{d+1-n}H-3,
\qquad
k_n=\frac{x+2y-a_n-7-3n}{2}.
\]
Because \(d+1-n\ge1\) and \(H\ge344\), \(a_n\) is odd and \(a_n\ge3\). The numerator defining \(k_n\) is even. Moreover,
\[
2k_n-a_n
=x+2y-2a_n-7-3n
\ge y-2-3n>0,
\]
where \(2a_n\le x+y+1-6\), \(n\le d<2m-6<2m\), and \(y>6m+2\). Thus \(k_n\ge1\) and \(a_n<2k_n\). Both equations of the complete odd-left inverse branch hold, so the exact inverse theorem gives the edge.

We therefore obtain the exact parent set
\[
\boxed{\left\{(a_n,k_n): n=0,2,4,\ldots,\ n\le d\right\}.}
\]
There are exactly
\[
\boxed{\lfloor d/2\rfloor+1}
\]
immediate parents of \(R_z\). No \(a=1\), \(a=0\), direct, or even-left parent has been omitted.

## The fan is unbounded over the parameter family

For every \(r\ge1\), the odd coefficient \(519\) is invertible modulo \(2^r\). There is therefore a residue \(z_r\pmod{2^r}\) satisfying
\[
519z_r+73\equiv0\pmod{2^r}.
\]
Every \(z=z_r+2^r t\) has \(d\ge r\), so the exact fan contains every even depth \(n\le r\). Thus the number of immediate parents is unbounded over this low-stop subfamily.

This rules out a fixed finite list of odd-left depths as a uniform treatment of \(m=512z+67\). It does **not** prove that any of these targets is unreachable: all parent branches must still be excluded recursively or by a stronger forward invariant.

## Reusable quotient residues

The formulas also give a compact M16 probe. Write \(n=2r\) and
\(s=(F(z)/2^n)\bmod16\). Since the dyadic terms in the explicit formulas have exponents greater than four throughout this family,
\[
a_n\equiv-2s-3\pmod{16},\qquad
k_n\equiv s+5-3r\pmod{16}.
\]
For fixed \(n\), as \(z\) ranges over \(2^n\mid F(z)\), the value \(s\pmod{16}\) ranges over all 16 residues because \(519\) is odd. This gives a finite 16-cell family for each \(n\bmod32\), suitable for checking against Agent 43's already-certified M16 CCert.seen table. Such a check can eliminate a branch only if every possible parent cell in that branch is absent.

## Trust boundary and next work

The derivation uses the exact, unbounded inverse predicate in
[FullSectionInverse.lean](../agent3-c-bounce-inverse/FullSectionInverse.lean). The displayed parent set is an algebraic consequence of that predicate, but this specialization has **not** been compiled in Lean 4.36.0-rc2. A local shell invocation returned a tool-level ClientError before executing the command; no local compile is claimed.

The highest-value next steps are:
1. formalize this exact parent-set equivalence against the unchanged source secNext;
2. check the 16 M16 quotient cells for each n mod32 before attempting deeper symbolic expansion;
3. derive a uniform recursive invariant for the surviving parent branches, rather than collecting isolated residue cylinders.

Keep this material in im-results/. It is a structural intermediate result, not a publishable Machine C decision or a BB(6) solution.
