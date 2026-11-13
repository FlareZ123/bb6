# Generic 3-adic Hensel selector for affine-exponential numerators

**Status: mathematical lemma and proof design; no Lean implementation or CI claim yet.** This is a reusable abstraction for the Q, T, and next-layer R numerators in the #746 inverse-parent work.

## 1. General setup

Fix integers \(A,B,C\) and natural numbers \(e_0,n_0\). Define
\[
F(h)=A\,2^{e_0+6h}+B(n_0+6h)+C,\qquad h\in\mathbb N.
\]
Assume
\[
F(0)\equiv0\pmod3,\qquad B\not\equiv0\pmod3.
\]
The first condition is sector-stable: \(2^{e_0+6h}\equiv2^{e_0}\pmod3\) and \(6Bh\equiv0\pmod3\), so \(3\mid F(h)\) for every h.

Let \(D_k=6\cdot3^k=2\cdot3^{k+1}\). For \(r\in\{0,1,2\}\), the existing power-period lemma gives
\[
3^{k+2}\mid 2^{rD_k}-1.
\]
Consequently the exponential part disappears modulo \(3^{k+2}\), while the linear part changes by
\(6Br3^k=2Br3^{k+1}\). The exact digit-shift law is therefore
\[
\boxed{F(h+r3^k)\equiv F(h)+2Br3^{k+1}\pmod{3^{k+2}}.}
\]

## 2. Unique Hensel selector

Define \(\rho_0=0\). Suppose \(3^{k+1}\mid F(\rho_k)\), and put
\[
q_k=F(\rho_k)/3^{k+1}.
\]
The shift law gives
\[
3^{k+2}\mid F(\rho_k+r3^k)
\iff q_k+2Br\equiv0\pmod3.
\]
Because \(2B\) is a unit modulo three, exactly one digit \(r\in\{0,1,2\}\) satisfies this condition. Define
\[
\rho_{k+1}=\rho_k+r3^k.
\]
The period-one consequence \(F(h+3^k)\equiv F(h)\pmod{3^{k+1}}\) lets every h reduce to its canonical residue modulo \(3^k\). Induction then proves
\[
\boxed{3^{k+1}\mid F(h)\iff h\bmod3^k=\rho_k.}
\]
Thus every affine-exponential numerator satisfying the two hypotheses has exactly one index cylinder at every 3-adic precision. At the next digit, one of the three lifts continues to higher valuation and the other two have exact valuation \(k+1\).

In the existing Lean convention, the digit is
\[
r=\operatorname{henselDigit}(q_k,-2B),
\]
since that function solves \(q_k-(-2B)r\equiv0\pmod3\).


### 3-adic isometry consequence

The same shift law gives more than uniqueness of the zero cylinder. If
\(h_1-h_2\) has exact 3-adic valuation k, write
\(h_1=h_2+r3^k+m3^{k+1}\) with \(r\in\{1,2\}\). The digit-shift
congruence at r, together with the period-one congruence for the
additional \(m3^{k+1}\), yields
\[
F(h_1)-F(h_2)\equiv2Br3^{k+1}\pmod{3^{k+2}}.
\]
Since \(2Br\) is nonzero modulo three,
\[
v_3(F(h_1)-F(h_2))=k+1
=v_3(h_1-h_2)+1.
\]
Thus \(F/3\) is a 3-adic isometry on the nonnegative integers and
extends uniquely by continuity to an isometry on \(\mathbb Z_3\).
More strongly, it is a bijection: for any target \(y\in\mathbb Z_3\),
the same unit-slope digit lift applied to \(F/3-y\) gives a unique
preimage. The compatible residues \(\rho_k\) are the finite truncations
of its unique 3-adic zero. On a deeper base cylinder where \(3^a\mid F\)
uniformly, the same argument after normalization gives the corresponding
isometry for \(F/3^a\).


## Scaled-cylinder version for nested layers

The same argument applies after a previously selected 3-adic cylinder. Let
\[
F(n)=A2^{n+c}+Bn+C,\qquad
n(u)=n_0+6\cdot3^a u,
\]
where \(a\ge0\), and suppose \(3^{a+1}\mid F(n(u))\) for every natural u. Define
\[
G(u)=F(n(u))/3^{a+1}.
\]
For \(r\in\{0,1,2\}\), shifting \(u\) by \(r3^k\) shifts both n and the exponent by \(6r3^{a+k}\). The exponential difference is divisible by \(3^{a+k+2}\), and the linear difference is \(2Br3^{a+k+1}\). After normalization,
\[
\boxed{G(u+r3^k)\equiv G(u)+2Br3^k\pmod{3^{k+1}}.}
\]
If \(3\nmid B\), then \(G(u)\bmod3\) is an affine function of u with unit slope \(2B\), so there is exactly one root digit modulo three. The same unique-digit induction continues at every precision. There is a compatible sequence \(\eta_k\) such that
\[
3^{a+k+1}\mid F(n_0+6\cdot3^a u)
\iff u\bmod3^k=\eta_k.
\]
Moreover G is a 3-adic isometry: if \(u_1-u_2\) has exact valuation k, the displayed shift law gives
\(v_3(G(u_1)-G(u_2))=k\). This scaled form is the appropriate abstraction for an R numerator restricted to one exact-Q lift; it does not require \(G(0)\) itself to vanish modulo three, because the first digit is selected rather than fixed to zero.

## 3. Instantiations already present in the repository

### Q numerator

Expanding Agent 44's numerator gives
\[
Q_j(n)=28\cdot2^n+B_Qn+C_Q,
\quad B_Q=-(2+2^{j+5}),\quad C_Q=15-3\cdot2^{j+4}.
\]
For even j, \(2^{j+5}\equiv2\pmod3\), so \(B_Q\equiv-4\equiv2\pmod3\). The Hensel coefficient \(-2B_Q\) is
\(4(1+2^{j+4})\), exactly Agent 44's index-shift coefficient. For sectors \(n\equiv4,5\pmod6\) and even j, the base numerator is divisible by three.

### T numerator

Expanding Agent 10's two-tier numerator gives
\[
T_j(n)=20\cdot2^n+B_Tn+C_T,
\quad B_T=-(22+2^{j+6}),\quad C_T=21-3\cdot2^{j+5}.
\]
For even j, \(2^{j+6}\equiv1\pmod3\), so \(B_T\equiv-23\equiv1\pmod3\). The generic coefficient \(-2B_T\equiv1\pmod3\), matching the unit coefficient in the existing twoTierNumerator shift theorem.

### Next-layer R numerator

Agent 7's next-layer formula is
\[
R_{t,\sigma}(n)=A\,2^{n+t-\sigma+4}+B_Rn+C,
\]
where
\[
B_R=-(2^{t+3}+2^{j+t+7}+2\cdot3^{t+3}).
\]
For even j, the exponents \(t+3\) and \(j+t+7\) differ by the even number \(j+4\), so the first two terms are equal nonzero residues modulo three; the final term vanishes. Hence \(B_R\not\equiv0\pmod3\). On any sector whose base value \(R(s)\) is divisible by three, the same unique-index Hensel recursion applies. Agent 7's first-digit table determines which of the two exact-Q lifts has this base divisibility.

## 4. Why this abstraction is useful

The Q-index, T-index, and R continuation proofs currently repeat the same architecture:

1. a period-digit expansion for \(2^{6r3^k}\);
2. a shift congruence modulo \(3^{k+2}\);
3. a quotient lift criterion;
4. uniqueness of a digit because the coefficient is a unit modulo three;
5. a recursive residue and an iff characterization.

The lemma above isolates steps 1–5 once. Each numerator then needs only:
- its \(A,B,C,e_0,n_0\) parameters;
- a proof of base divisibility modulo three;
- a proof that \(B\) is a unit modulo three.

This should support a shared core-Lean module and reduce proof drift between Agent 7, 10, and 44. It also provides a principled way to extend the selector to arbitrary nested parent numerators, rather than writing a new bespoke Hensel proof at every layer.

## 5. Scope boundary

This is a selector theorem, not a band theorem. It determines exactly which index cylinder has a prescribed 3-adic divisibility, but it does not prove that the associated quotient lies in the dyadic ResetParent image interval. The R numerator also needs a base-divisibility condition; the unit derivative alone does not guarantee that any lift exists. Keep this as intermediate research until a core-Lean implementation is compiled and instantiated against the actual source parent equations.


### Composition warning for parent chains

When composing selectors across successive ResetParent layers, do not
restrict the next layer to the two lifts having exact valuation at the
current layer. The current parent remains valid whenever its required
power of three divides the numerator; its odd quotient is allowed to
remain divisible by three. The next layer has a new affine-exponential
numerator and its unit derivative selects exactly one of all three
next-digit lifts. That selected lift may be the third, higher-valuation
lift of the previous numerator. This does not invalidate the previous
parent edge. Induction must retain the full divisibility cylinder, not
only its exact-valuation subset.
