# Exact fatal-spectrum pullback through a canonical #623 transition

**Status:** exact consequence of existing source-verified theorems, derived here as a paper-level composition. The combined pullback and bounds have not yet been packaged in one Lean consumer. This is intermediate mathematics, not a decision of the authentic blank-root orbit.

## 1. Canonical output coordinates

For a genuine blank-root section state \(D(a,d)\), the first counter \(a\) is even. Put
\[
q=\min(a,d),\qquad p=|a-d|,\qquad g=p-3q.
\]
Let \(\beta,\delta\) be the exact canonical-ray correction terms in
[RootRayGapCocycle.md](RootRayGapCocycle.md), and set \(T=\delta-\beta\).

The source-derived gap/scale cocycle gives the next state \(D(a',d')\) in the form
\[
(a'-d',q')=
\begin{cases}
(g-T,\;3q+\delta),&g\ge T,\\
(-(T-g),\;p+\beta),&g<T,
\end{cases}
\]
where \(q'=\min(a',d')\). Thus, with \(s=a'-d'\) and \(p'=|s|\), the output-side decision is exactly the sign of \(s\). The output third-counter parity is:
- odd for input sectors LO and RE;
- even for input sectors LE and RO.

## 2. Exact next-step fatality after substitution

Write
\[
E_b=\{x:\operatorname{drainB}(x,b,m)=\texttt{none}\},
\qquad \tau(x)=\frac{3^x-1}{2}.
\]
The set \(E_b\) is independent of \(m\). The source theorems
odd_even_none_iff_two_spectra and even_even_none_iff_three_spectra
in Agent 49's ExactOddSectorSource.lean and ExactEvenSectorSource.lean
give the complete next-step halt predicate for every positive-even first
counter. Substituting \(s=a'-d'\) yields:

| Output third-counter parity | Signed output gap \(s\) | Exact condition for \(D(a',d')\) to halt next |
|---|---:|---|
| odd | \(s\ge5\) | \(s-5\in E_{d'+3}\) |
| odd | \(s\le3\) | \(d'+4-a'\in E_{a'-1}\) |
| even | \(s\ge4\) | \(s-2\in E_{d'+2}\) |
| even | \(s=2\) | \(0\in E_{a'}\) |
| even | \(s\le0\) | evalA\((d'+1-a',a',2a'+5)\) fails, or it returns \((x,b,m)\) with \(x\in E_b\) |

The parity of \(a'\) is even, so these cases are exhaustive. In particular, the equality case \(s=0\) belongs to the even right-hand predicate.

In terms of \(p',q'\), this becomes:
- odd output, left/far: \(p'\ge5\) and \(p'-5\in E_{q'+3}\);
- odd output, left/near: \(p'\in\{1,3\}\) and \(4-p'\in E_{q'+p'-1}\);
- odd output, right: \(p'\ge1\) and \(p'+4\in E_{q'-1}\);
- even output, left/far: \(p'\ge4\) and \(p'-2\in E_{q'+2}\);
- even output, diagonal: \(p'=2\) and \(0\in E_{q'+2}\);
- even output, right (including equality): \(p'\ge0\) and
  evalA\((p'+1,q',2q'+5)\) fails or returns a first counter in the corresponding \(E_b\).

This is the direct composition that was missing from the earlier Agent 1 cocycle note: it keeps the exact recursive fatal spectrum, rather than replacing it by only a terminal ratio window.

## 3. First-threshold consequence for every fatal spectrum member

The source theorem drainB_safe_ones says that \(b\le\tau(x)\) forces
\(\operatorname{drainB}(x,b,m)\ne\texttt{none}\). Therefore
\[
x\in E_b\quad\Longrightarrow\quad
b\ge\tau(x)+1
\quad\Longrightarrow\quad
3^x\le2b-1.
\]

Applying this to the table gives the following exact necessary inequalities:

| Output case | Necessary inequality |
|---|---|
| odd, left/far | \(3^{p'-5}\le2q'+5\) |
| odd, left/near | \(p'\le3\) |
| odd, right | \(3^{p'+4}\le2q'-3\) |
| even, left/far | \(3^{p'-2}\le2q'+3\) |
| even, diagonal | \(p'=2\) |
| even, right | \(3^{p'}\le2q'-1\) |

For the last row, the evaluator-failure alternative gives
\(q'\ge\tau(p'+1)\), hence \(3^{p'}\le2q'-1\). If the evaluator succeeds, write its exact ternary decomposition as
\[
2q'-1=3^v(6b+1+4\varepsilon),\qquad
x=p'-v+2\varepsilon,\qquad \varepsilon\in\{0,1\}.
\]
If \(x=0\), then \(p'\le v\) and \(3^{p'}\le3^v\le2q'-1\).
If \(x>0\), the downstream fatality \(x\in E_b\) gives
\(3^x\le2b-1\), whence
\[
3^{p'}\le3^{v+x}\le3^v(2b-1)<2q'-1.
\]
Thus the even-right bound covers both failure mechanisms, not just the initial evaluator.

## 4. A branch-sensitive logarithmic output-gap bound

Assume the existing \(n\ge10\) terminal-parent hypotheses with \(K=n+6\).
The source joint-mass bounds for the four canonical drains are
\[
\begin{array}{c|c}
\text{input sector}&a'+d'\text{ upper bound}\\ \hline
\mathrm{LO}&x+2y+10+3n\\
\mathrm{LE}&x+2y+7+3n\\
\mathrm{RO}&y+2x+5+3n\\
\mathrm{RE}&y+2x+5+3n.
\end{array}
\]
Combining these with the already source-certified TerminalRatio4
inequalities (and \(q\le3^n\)) gives
\[
a'+d'\le6q+12n+28\le6\cdot3^n+12n+28.
\]
For \(n\ge10\),
\[
2q'+5\le a'+d'+5
\le6\cdot3^n+12n+33
<9\cdot3^n=3^{n+2}.
\]
Consequently the exact fatal-spectrum inequalities above imply:

| Successor sector | Bound on \(p'=|a'-d'|\) |
|---|---:|
| odd, left/far | \(p'\le n+6\) |
| odd, left/near | \(p'\le3\) |
| odd, right | \(p'\le n-3\) |
| even, left/far | \(p'\le n+3\) |
| even, diagonal | \(p'=2\) |
| even, right | \(p'\le n+1\) |

In particular, every terminal successor has \(p'\le n+6\), improving the generic \(K+4=n+10\) output-gap interface used in the original ratio-4 cancellation argument. The branch-sensitive bounds are stronger and should be passed to the same bridge arithmetic separately, rather than collapsed immediately to the uniform maximum.

## 5. What this does and does not establish

The exact fatal-spectrum pullback and the logarithmic successor-gap bounds are source-derived consequences of:
- Parity623Source.lean (drainB_safe_ones, exact evaluator failure congruence);
- ExactOddSectorSource.lean and ExactEvenSectorSource.lean (complete one-step fatality predicates);
- JointMassSource.lean (four joint-mass envelopes);
- TerminalRatio4Source.lean (the four predecessor ratio windows).

The combined derivation is not yet a single Lean-checked theorem. It does not show that the authentic \(D(0,7)\) orbit avoids the resulting preimage set, and it does not prove #623 nonhalting or determine BB(6).

**Best next use:** formalize the pullback/output-gap bounds as a consumer of the existing source modules, then feed their branch-sensitive values into the ratio-4 bridge cancellation. The key remaining root problem is still an all-time invariant excluding the exact recursive \(E_b\) preimages, not another finite root scan.
