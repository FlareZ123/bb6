# The \(t=3\) high-\(q\) gate is one residue class modulo \(4374\)

**Agent 10, 7 November 2026.** Intermediate result for the unresolved #746 source-C reset problem. The congruence classification below is an exact paper-level derivation. The finite inverse-cone census is reproducible computation. Neither establishes global nonreachability or a BB(6) value.

## 1. Source-C branch being isolated

Write
\[
D_j(n)=\operatorname{deficit}(n,j),\qquad
U_j(n)=4\cdot2^n-D_j(n),\qquad
Z_j(n)=2U_j(n)+5.
\]
The already source-checked closed deficit identity is
\[
D_j(n)+(n-1)=2^j(2n+3),
\]
so
\[
Z_j(n)=8\cdot2^n+2n+3-(2n+3)2^{j+1}. \tag{1}
\]

For \(n\ge20\), \(n\bmod6\in\{4,5\}\), and the source margin
\[
2048D_j(n)+16384n+16384\le2^n,
\]
the exact \(t=3\) parent-band theorem fixes the dyadic scale at \(k=n-3\). Thus a \(t=3\) first-reset parent \(q\) of \(U_j(n)\) satisfies
\[
Z_j(n)=81d,\qquad
16d=2^n+q+n+2,
\]
and hence
\[
q=16d-2^n-n-2. \tag{2}
\]
The selector **RayTThreeDoubleSelector.lean** retains the high-\(q\) subcase
\[
81\mid 2q+5. \tag{3}
\]

The other \(t=3\) selector subcase, involving all admissible \(t=0\) parents of \(q\), is not covered by this note.

## 2. Exact translation to a shifted \(3\)-adic congruence

Substitute (2):
\[
2q+5=32d-2^{n+1}-2n+1.
\]
Since \(Z_j(n)=81d\), define
\[
c_n\equiv 38(2^{n+1}+2n-1)\pmod{81},
\qquad 0\le c_n<81,
\]
using \(32\cdot38\equiv1\pmod{81}\). Then
\[
\boxed{
81\mid(2q+5)
\quad\Longleftrightarrow\quad
Z_j(n)\equiv81c_n\pmod{3^8}.
} \tag{4}
\]
Indeed, (3) is equivalent to \(81\mid(d-c_n)\), and \(Z_j(n)=81d\).

This is a *translated* depth-eight congruence. It is generally not the zero-divisibility condition \(3^8\mid Z_j(n)\) from **RayDepthResidue.lean**; the target quotient \(c_n\) is usually nonzero.

## 3. Exactly one index residue modulo \(4374\)

Equation (1) and (4) give
\[
2^{j+1}\equiv
(2n+3)^{-1}\bigl(8\cdot2^n+2n+3-81c_n\bigr)
\pmod{6561}. \tag{5}
\]
For \(n\equiv4,5\pmod6\), both factors on the right are units modulo \(3\):
- \(2n+3\equiv2,1\pmod3\), respectively;
- \(8\cdot2^n+2n+3\equiv1,2\pmod3\), respectively, and \(81c_n\equiv0\pmod3\).

Thus the right side of (5) is a unit modulo \(3^8=6561\).

The multiplicative order of \(2\) modulo \(3^8\) is
\[
\operatorname{ord}_{3^8}(2)=2\cdot3^7=4374.
\]
For completeness, \(2^m\equiv1\pmod3\) forces \(m=2s\). The elementary \(3\)-adic valuation identity
\[
v_3(4^s-1)=1+v_3(s)
\]
follows by first observing \(4^r\equiv1+3r\pmod9\) when \(3\nmid r\), then using
\[
x^3-1=(x-1)(x^2+x+1)
\]
to increase the valuation by exactly one whenever \(x\equiv1\pmod3\). Consequently, \(4^s\equiv1\pmod{3^8}\) forces \(3^7\mid s\). Conversely, \(v_3(4^{3^7}-1)=8\), so \(2^{4374}\equiv1\pmod{3^8}\). This proves the claimed order.

There are exactly
\[
\varphi(3^8)=3^8-3^7=4374
\]
units modulo \(3^8\). Therefore the powers \(2^{j+1}\), for \(0\le j<4374\), enumerate all units exactly once. Equation (5) has exactly one solution \(j_0(n)\) in that interval. Since \(2^{4374}\equiv1\pmod{6561}\), the complete solution set is
\[
\boxed{j\equiv j_0(n)\pmod{4374}.} \tag{6}
\]

Thus, after the exact \(t=3\) band reduction, the high-\(q\) gate is a single index residue class modulo \(2\cdot3^7\), for every surviving \(n\)-sector. This gives a precise interface with Agent 7's depth-period and Hensel-lift work, with a nonzero shifted target \(81c_n\).

## 4. Reproducible finite inverse-cone audit

**t3_high_gate_audit.py** implements the two exact source-C ResetParent arms from **FirstInverseComplete.lean**:
- even parent: \(6\cdot2^k-1\le u\le8\cdot2^k-3\), \(2u=8\cdot2^k+h+k\);
- odd parent: \(2u+5=3^{t+1}d\), \(d\) odd, \(6\cdot2^k+1\le2^td\le8\cdot2^k-1\), \(2(2^td)=8\cdot2^k+h+k+5\).

It enumerates *all* admissible odd valuations, not a fixed valuation cutoff. Strict decrease of every valid parent is source-proved in **ResetParentStrict.lean**. The script first finds the unique \(j_0(n)\) in (6), then enumerates all \(j=j_0+4374m\) satisfying the source margin. For each resulting \(q\), it computes the complete finite reverse ancestor cone and tests whether root height \(2\) occurs.

Reproduce with:
~~~bash
python im-results/agent10-cascade/t3_high_gate_audit.py
~~~

Exact integer-arithmetic census for \(20\le n\le10000\), \(n\bmod6\in\{4,5\}\):
- 3,801 \((n,j)\) high-\(q\) candidates, across 2,595 distinct \(n\);
- per-index candidate multiplicities: 1 candidate for 1,458 indices, 2 for 1,068, and 3 for 69;
- \(v_3(2q+5)\) ranged from 4 through 11, with counts \(2525,858,285,86,29,14,3,1\);
- the second \(t=3\) parent height \(r\) had residues \(r\bmod3=0,1,2\) in counts \(1255,1276,1270\);
- every computed reverse cone omitted \(2\); cone sizes ranged from 4 to 57 (median 6, mean \(7.522757\)); maximum path depth was 25.

The largest cone had 57 nodes at \((n,j)=(8638,2438)\). The greatest depth, 25, occurred at \((6298,3038)\). No search cap was reached; termination follows from the strict parent decrease and the script checks that every enumerated parent is smaller than its target.

**Evidence boundary:** the congruence class (6) is a paper-level exact derivation. The counts and reverse-cone exclusions are a finite computational census through \(n=10000\). They are not a proof that all high-\(q\) targets are unreachable for arbitrary \(n\), and the script is not a substitute for a Lean-checked universal closed-cone certificate.

## 5. What remains

The new classification reduces the high-\(q\) branch to one residue class modulo \(4374\), but does not resolve its authentic-root status. The finite census suggests that the exact reverse cones may be tractable, although their size grows with the \(3\)-adic valuation and no uniform bound has been established.

Next steps:
1. Mechanize the shifted-target Hensel lift \(Z_j(n)-81c_n\) by adapting **RayDepthHensel.signedZ_lift_criterion**.
2. Reconcile the residue class (6) with **RayDepthResidue.depthResidue** and derive a direct recursive digit formula for \(j_0(n)\).
3. Prove a root-sensitive exclusion for all high-\(q\) candidates, including every odd valuation in their complete inverse cones.
4. Continue the separate all-\(t=0\)-parent selector branch; this note does not subsume it.

No result here determines whether machine #746 halts or the exact value of BB(6).


## 6. Formalized translated tower and precision-nine second-parent selector (Agent 7, 7 November 2026)

The shifted-target Hensel lift and the exact source-equation bridge are now formalized in [Agent 7's TranslatedDepthResidue.lean](../agent7-fatal-density/TranslatedDepthResidue.lean).

- `translatedDepthResidue_iff` proves, for every offset divisible by (81), exactly one depth class modulo (2\cdot3^{k+3}) at precision (3^{k+4}).
- `tThreeHighGate_iff` proves that the source equations (Z_j(n)=81d) and (16d=2^n+q+n+2) make (81\mid(2q+5)) equivalent to the translated precision-eight condition.
- `tThreeHighGate_residue_iff` therefore makes (6) a kernel-checked source-gate residue class modulo (4374), not only a paper derivation.
- Define (X_n=2^{n+1}+2n-1), (K_n=(32c_n-X_n)/81), and (A_{0,n}=81c_n+6561(K_n+1)). The new theorem `tThreeHighSecondParent_mod_zero_iff` proves that, under the exact second-parent equation and (n\ge20), (n\bmod6\in\{4,5\}),
  [
  r\equiv0\pmod3
  \quad\Longleftrightarrow\quad
  3^9\mid Z_j(n)-A_{0,n}.
  ]
  The translated tower makes this one unique class modulo (13122). It identifies precisely the (r\bmod3=0) branch already handled by `third_high_child_zero_root_dead`; the other two lifted classes remain unresolved.

Full unchanged-source Lean runs [42403440784](https://github.com/FlareZ123/bb6/actions/runs/42403440784), [42404035998](https://github.com/FlareZ123/bb6/actions/runs/42404035998), and [42404919018](https://github.com/FlareZ123/bb6/actions/runs/42404919018) succeeded. The new theorem audits report only standard logical axioms, with no `sorryAx`.

An independent forward-orbit audit is also recorded in [ForwardOrbitAudit100k.md](../agent7-fatal-density/ForwardOrbitAudit100k.md), with executable script [t3_high_gate_forward_audit.py](../agent7-fatal-density/t3_high_gate_forward_audit.py). It checked 245,399 high-(q) candidates through (n=100000) against the deterministic blank-root reset orbit and found zero matches. This is finite exact-integer evidence, not a universal exclusion. The existing reverse-cone census through (n=10000) remains a separate exhaustive finite check.

**Updated remaining task:** prove or refute root reachability in the (r\bmod3=1,2) lifted classes, including all possible (t=0) and higher-valuation parents. The formal residue selectors do not by themselves close those branches or establish halting of the original machine.


## 7. Tight geometry of the second t=3 parent (Agent 7, 7 November 2026)

A further arithmetic reduction is formalized in [TThreeHighTightBounds.lean](../agent7-fatal-density/TThreeHighTightBounds.lean). Write (p=2^{n-4}=4\cdot2^k), (k=n-6), and let (r) be the second (t=3) parent. From the exact source equations and the expanded margin inequality
[
2048(2n+3)2^j+14336n+18432\le2^n,
]
the Lean arithmetic package derives
[
10934p-961n+18609\le6561r\le10942p-10177n+6321.
]
It then derives the scaled strict inequalities
[
3p<2r+5<\frac92p,
\qquad
\frac94p<2r+5<\frac{27}{8}p.
]
Equivalently, whenever the relevant quotients are integral,
[
4\cdot2^k<\frac{2r+5}{3}<6\cdot2^k,
\qquad
2\cdot2^k<\frac{2(2r+5)}9<3\cdot2^k.
]

The first quotient is in the dyadic gap between odd-parent bands at scales (k-1,k). The second is in the gap between scales (k-2,k-1). Hence no odd parent of (r) can have exponent (t=0) or (t=1). Any remaining odd parent must have (t\ge2). This matches the finite reverse-cone census, where the first observed odd parents of (r) have (t=2,4,6).

The file proves the linear implication from the Int-cast source equations and margin hypotheses, and proves the scaled gap inequalities. It does not yet provide the Nat-to-Int margin bridge or compose the gap result with the complete reset-parent grammar. Full unchanged-source CI is queued as [42407885455](https://github.com/FlareZ123/bb6/actions/runs/42407885455). This reduction is not a proof that (r) is root-dead; higher odd-parent exponents (t\ge2) remain to be analyzed.
