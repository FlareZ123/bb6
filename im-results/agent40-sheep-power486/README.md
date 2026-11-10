# Sheep: exact sixth-3-adic direct power-parent census

**Intermediate mathematical result, 10 November 2026.** For the authentic first-even return map \(E\) of the six-state Sheep machine

1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE,

the complete legal nonterminal even predecessor fiber of the power \(Y=2^{486t}\), for **every \(t\ge1\) with \(3\nmid t\)**, has size

\[
\boxed{\#E^{-1}(2^{486t})=
3\,\mathbf1_{t\bmod2=1}
+\mathbf1_{t\bmod4=2}
+\mathbf1_{t\bmod7=1}
+\mathbf1_{t\bmod9=2}.}
\]

Each indicator represents a distinct, genuine incoming original-machine section edge. The exact six possible source sectors \((h,a)\), where \(h\) is the hidden odd-block length and \(a\) is the source's 2-valuation, are:

| Hidden steps \(h\) | Source valuation \(a\) | Exact existence condition |
| ---: | ---: | --- |
| 1 | 1 | \(t\equiv1\pmod2\) |
| 1 | 3 | \(t\equiv2\pmod4\) |
| 3 | 1 | \(t\equiv1\pmod2\) |
| 3 | 6 | \(t\equiv1\pmod7\) |
| 5 | 1 | \(t\equiv1\pmod2\) |
| 6 | 2 | \(t\equiv2\pmod9\) |

**Authentic blank-root corollary.** For every positive \(t\) satisfying

\[
3\nmid t,\quad t\equiv0\pmod4,\quad
t\not\equiv1\pmod7,\quad t\not\equiv2\pmod9,
\]

the original Sheep blank computation, whose first even section is **10**, cannot reach \(2^{486t}\). There are exactly **30 residue classes of \(t\) modulo 252** satisfying this condition, or 30 excluded exponent residues modulo \(486\cdot252=122472\). Their natural density among positive halting exponents is

\[
\boxed{\frac{30}{122472}=\frac5{20412}\simeq0.0244954\%.}
\]

For example, \(2^{1944+122472k}\) has no legal first-even predecessor for every \(k\ge0\). These new exponents belong to the sixth 3-adic valuation stratum, beyond the previously completed fourth and fifth strata, and they are disjoint from all **28 expressly compared** older E-cone progressions in the certificate. They also have five genuine ordinary F ancestors, so the earlier F-depth-five absence test cannot exclude them. They do **not** establish Sheep nonhalting or determine BB(6).

## Source mathematics and infinite proof

Agent16's original six-state machine proof, [CI 41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547), proves the genuine first-even section semantics, including initial input 10 and the halting condition that an even power of two is reached. For a nonterminal even source \(x=2^a v\), \(a\ge1\), odd \(v\ge3\), the ordinary return is

\[
F(x)=\begin{cases}
x+a+3,&v=3,\\
x+a+(v-1)/2,&v\ge5.
\end{cases}
\]

If \(F(x)-1=2^h u\) with odd \(u\), then the true next even section is \(E(x)=1+3^h u\). Reaching a target greater than 10 requires a last incoming edge.

**Hidden-length ceiling.** Since \(2^{486}\equiv730=1+729\pmod{2187}\), lifting the exponent shows \(v_3(2^{486t}-1)=6\) for every \(3\nmid t\). Thus a predecessor can have only \(0\le h\le6\).

**Every generic source, including arbitrarily large valuations.** If \(v\ge5\), the source equations reduce exactly to

\[
3^h(2^{a+1}+1)v+2a3^h+2^{h+1}
=2^{486t+h+1}+3^{h+1}.
\]

Put \(D=3^h\), \(M=D(2^{a+1}+1)\), and \(K=D(2a-3)+2^{h+1}\). A necessary congruence is

\[
2^{486t+h+1}\equiv K\pmod M.
\]

For \(h=0\), \(a\ge2\) is impossible. For \(1\le h\le6\), \(a\ge2h+3\) is impossible: at these cutoffs the odd integer \(K\) satisfies \(1<K<2^a\), and this interval is preserved as \(a\) increases because \(K(a+1)-K(a)=2D\le2^a\). Modulo \(2^{a+1}+1\), a power of two has signed-power residue \(\pm2^r\) with \(0\le r\le a\); none equals such an odd \(K\). This is the signed-power-gap lemma already established in the prior Sheep work.

Precisely **55 pairs \((h,a)\)** remain. For each, the exact order \(o\) of 2 modulo \(M\) gives a complete period \(q=o/\gcd(o,486)\) in \(t\). All **429 residue representatives** over the 55 periods are checked by the deterministic standard-library [certificate](certificate.py); maximum \(q=45\). Exactly six rows survive, each with one residue as listed above. The [Lean generator](generate_lean.py) produces four modules. **SheepPower486Core** proves the unbounded period reduction; **SheepPower486Rows** kernel-checks all 55 complete residue assertions; **SheepPower486All** proves that any generic source within the cutoff falls in one of the six rows; and **SheepPower486RootGate** proves their simultaneous exclusion for the stated forbidden \(t\)-classes. All four modules were locally compiled with Lean **4.36.0-rc2**, no sorry or admit, and printed exactly the standard axioms \([propext, Classical.choice, Quot.sound]\) for the combined final theorem. Their source equations agree with Agent14's original-source inverse splitter; they have **not** been imported into a new end-to-end six-state Lean machine theorem.

**Exceptional cofactor \(v=3\).** The exact required equality is

\[
2^{486t+h}+C=D(3\cdot2^a+a+3),\qquad C=D-2^h.
\]

For each \(h=0,\ldots,6\), set \(e=\lfloor\log_2(3D)\rfloor\), \(g=e-h\), \(L=3D-2^e>0\), \(U=2^{e+1}-3D>0\). At \(j=486\), the certificate checks

\[
L2^j>2^gC,\quad
U2^j>2^{g+1}(D(j+3)-C),\quad
U2^j\ge2^{g+1}D.
\]

They remain valid for all \(j\ge486\), because the exponential margin grows faster than the linear correction. Splitting \(a\ge j-g\) from \(a<j-g\) makes the main power term respectively too large or too small for the residual \(D(a+3)-C\). This rules out every exceptional source for every target in the theorem.

**Sufficiency and distinctness.** Whenever one of the six modular conditions holds, its source is uniquely

\[
x_{h,a}(t)=2^a\,\frac{2^{486t+h+1}-K}{M}.
\]

The complete-period congruence makes this an integer; the numerator and odd denominator make its cofactor odd, and \(t\ge1\) makes it at least five. Substitution yields \(F(x)-1=2^h(2^{486t}-1)/3^h\), with odd residual quotient. Hence the source has **exactly \(h\)** hidden odd steps and \(E(x)=2^{486t}\). Distinct pairs \((h,a)\) produce distinct actual sources because a deterministic E edge fixes both a and h.

## Reproduction, originality, and unresolved work

Run Python 3.10+ **certificate.py** without dependencies. Run **generate_lean.py** from this directory in a normal repository clone, with the sibling [SheepPower648Core.lean](../agent40-sheep-648-parents/SheepPower648Core.lean) present. Compile the generated Lean modules in the order Core, Rows, All, RootGate, adding the generation directory to LEAN_PATH. The proof is over all \(t\), rather than a finite bounded search. Its original-source semantic bridge is a separately successful older proof.

The 30 excluded exponent classes are disjoint from the 28 earlier explicitly enumerated E-cone families; each CRT intersection check uses \((486t-b)\bmod\gcd(122472,P)\). Fourth/fifth stratum exclusions are disjoint by exact 3-adic valuation. The older 17-stratum sieve restricted to exponents divisible by 17496 belongs to a strictly higher valuation sector. External academic priority and overlap with every other repository certificate have **not** been exhaustively established.

This is a publishability-unqualified **intermediate result**, retained under im-results. It supplies a complete additional direct-parent census and an authentic infinite blank-root exclusion. There remain infinitely many admissible power targets with genuine parents, and the all-time actual orbit from 10 remains unresolved. The useful next mathematical task is a history-sensitive invariant that excludes the surviving direct-parent roots, or an authentic halting witness.
