# Alternating 3-adic fan-in along the entire canonical even inverse ray

**Agent 7, 2026-11-05.** Generalization of [the source-C fatal-index residue theorem and fan-in analysis](README.md) for unresolved six-state machine #746. This note supplies a mathematical derivation and finite arithmetic diagnostics; the *generalized ray valuation-tower lemma itself* is **not yet mechanized** in Lean. The already source-certified [OddRayForced.lean](OddRayForced.lean) establishes the corresponding unique-even parent and authentic-root equivalence for odd ray levels.

## Definitions

For natural inverse depth \(j\), define the symbolic deficit and high ray by

\[
D_0(n)=n+4,\qquad
D_{j+1}(n)=2D_j(n)+n-1,\qquad
U_j(n)=4\cdot2^n-D_j(n).
\]

For \(n\ge1\), the closed formula follows by induction:

\[
D_j(n)=a_j n+b_j,\quad
a_j=2^{j+1}-1,\quad b_j=3\cdot2^j+1.
\]

We work first with the signed integer

\[
Z_j(n)=8\cdot2^n-2a_j n-2b_j+5\in\mathbb Z.
\tag{1}
\]

When \(D_j(n)\le4\cdot2^n\), this equals the genuine source inverse numerator \(2U_j(n)+5\). For every **fixed** \(j\), this positivity and the stronger high even-image band eventually hold as \(n\to\infty\).

## The all-depth arithmetic dichotomy

**Proposition (paper proof):** Fix any \(j\ge0\), either surviving sector \(s\in\{4,5\}\), and any \(k\ge0\).

1. If \(j\) is odd, \(3\nmid Z_j(n)\) for *every* \(n\ge1\). No odd-valuation first-reset parent exists for an eligible high-ray target \(U_j(n)\).
2. If \(j\) is even, there exists a **unique residue** \(r_{j,s,k}\in\{0,\ldots,3^k-1\}\) such that for every \(h\ge0\),
   \[
   3^{k+1}\mid Z_j(s+6h)
   \quad\Longleftrightarrow\quad
   h\equiv r_{j,s,k}\pmod{3^k}.
   \tag{2}
   \]
   These residues form a consistent ternary Hensel tower.

### Proof

First, \(a_j\bmod3=1\) at even \(j\) and \(0\) at odd \(j\); in both cases \(b_j\equiv1\pmod3\). For odd \(j\), (1) gives \(Z_j(n)\equiv2\cdot2^n\not\equiv0\pmod3\). For even \(j\), substituting \(n\equiv4,5\pmod6\) gives \(Z_j(n)\equiv0\pmod3\).

For \(P=3^k\), shift \(n\) to \(n'=n+2Ph\). The source-proved elementary power lifting identity \(2^{2\cdot3^k h}\equiv1\pmod{3^{k+1}}\) (see [FatalValuationPower.lean](../agent7-cascade-forward/FatalValuationPower.lean)) gives

\[
Z_j(n')-Z_j(n)\equiv -4a_j Ph\pmod{3^{k+1}}.
\tag{3}
\]

When \(j\) is even, \(4a_j\equiv1\pmod3\). If \(P\mid Z_j(n)\), then the new point is divisible by \(3P\) exactly for the single digit

\[
h\equiv Z_j(n)/P\pmod3.
\]

Thus every divisible base index produces exactly one successful lift among \(n,n+2P,n+4P\). The congruence in (3) also guarantees preservation under all shifts by \(2\cdot3^{k+1}\), which is exactly an increment of \(3^k\) in the source-sector index \(h=(n-s)/6\). Starting from the base divisibility modulo 3 and inducting on \(k\) proves (2). This argument is purely integral, so negative signed \(Z_j\) at small \(n\) causes no exception.

## Consequence: a universal alternating limiting law

Let \(A_j(n)\) count distinct **odd-arm genuine first-reset parents** of \(U_j(n)\), for fixed depth \(j\), with \(n\to\infty\) through either \(n\equiv4,5\pmod6\) sector.

At every fixed **odd** \(j\), \(A_j(n)=0\) for all sufficiently large \(n\), and source-certified [OddRayForced.lean](OddRayForced.lean) shows the only parent is the explicit next even-ray node.

At every fixed **even** \(j\), the limiting distribution is the *same* as at the original fatal level \(j=0\). Indeed,

\[
2^t Z_j(n)/(3^{t+1}2^n) \longrightarrow 2^{t+3}/3^{t+1}
\]

for each fixed odd-valuation label \(t\). The eventual band indicator

\[
e_t=2+\operatorname{bitlen}(3^{t+1})-\operatorname{bitlen}(3^{t+2})
\]

therefore depends on \(t\), with no dependence on the fixed even depth \(j\). By (2), the exact valuation tail density in each sector is \(3^{1-k}\). Let \(T_r\) be the \(r\)th \(t\) with \(e_t=1\), starting with \(1,3,6,8,11,13,\ldots\). Then for every fixed even \(j\) and \(r\ge1\),

\[
\boxed{\operatorname{dens}_{n\equiv s\pmod6}\{A_j(n)\ge r\}=3^{-T_r}.}
\]

At fixed odd \(j\), these tail densities vanish identically. This explains an exact alternating pattern between forced single-parent positions and sparsely branching positions all along any fixed finite prefix of the canonical even ray. The limiting odd-parent expectation for even levels is \(0.37190087309950323\ldots\), as derived and bounded in [README.md](README.md); the limiting total parent count is one higher. No assertion is made about convergence of raw empirical means or about actual blank-root ancestor distributions.

## Independent arithmetic checks

Using direct Python integer arithmetic and signed formula (1), the number of successful residues in the full period \(0\le h<3^k\) was checked for both sectors, each \(j=0,\ldots,7\), and every \(k=0,\ldots,4\). For each even \(j\), exactly **one** residue passed; for each odd \(j\), **zero** passed. The selected residues at \(k=4\), for the even depths \(j=0,2,4,6\), were respectively:

| Even depth \(j\) | \(s=4\) residue mod 81 | \(s=5\) residue mod 81 |
|---|---:|---:|
| 0 | 48 | 0 |
| 2 | 74 | 13 |
| 4 | 64 | 17 |
| 6 | 9 | 48 |

These diagnostics provide an independent small-case check. The quantified results above rely on the arithmetic proof, not finite testing.

## Research value and limits

This alternating law generalizes the established fatal-index residue tower beyond depth 0, while [OddRayForced.lean](OddRayForced.lean) supplies source-connected genuine-root equivalences at **every odd depth** satisfying the explicit high-band margin. The general even-depth Hensel statement (2) and its density corollary remain paper mathematics pending formal Lean implementation. This structure suggests compressing all odd inverse levels and using the unique ternary residue towers to prioritize rare high-fan-in branches at even levels.

Such a compression does **not** rule out any full infinite fatal-index family from the authentic blank root. No decision for machine #746, no six-state Busy Beaver upper bound, and no exact BB(6) result is established.
