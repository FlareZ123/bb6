# A source-certified modular inverse-cone sieve for Machine C's high stopping family

## Result

Write the unified stopping parameters as \(J\ge 1\), \(m\ge 0\), with target coordinates
\[
x=2J+1,\qquad k+J+3m+4=2^{2m+2}(J+2).
\]
The modular inverse-cone checker is applied to the residue pair
\[
(J,m)\longmapsto (2J+1,-J-3m-4)\pmod {2^b}.
\]

Define
\[
b(J,m)=\min\!\left(32,\,2m+\begin{cases}2&J\ge2,\\1&J=1,\end{cases}\right),
\]
and let \(E_b(J,m)\) be the Boolean predicate excluded b (stopResidue J m) in the formal development.

The original-source Lean theorem
BB6.Agent42ModularCone.high_stop_excluded proves:
\[
E_{b(J,m)}(J,m)=\mathrm{true}
\quad\Longrightarrow\quad
\neg\,\mathrm{CReach}(2J+1,k)
\]
for every \(k\) satisfying the stopping equation above.

This is a source-connected theorem, not merely a quotient calculation. Its proof instantiates the generic modular inverse-cone theorem with the original Machine C parent law and forbidden odd-image law. The size invariant is \(y+2\ge 3\cdot2^b\); it is supplied by the stopping equation at the stated precision. No relative-growth hypothesis such as \(J\le3m+1\) is used.

The fixed eight-bit specialization high_stop_excluded8 applies for \(J\ge2\), \(m\ge3\). Its predicate depends only on the pair of residues modulo 256. Every accepted residue pair therefore describes an infinite family of compatible high-stop parameters (taking sufficiently large lifts to meet \(J\ge2,m\ge3\)).

## Exact eight-bit census

An exhaustive evaluation of the finite checker over all \(256^2\) residue pairs gives:

| Quantity | Count |
| --- | ---: |
| Accepted high-stop residue pairs | 39,506 / 65,536 |
| Accepted immediately by the root forbidden-image test | 16,384 |
| Accepted only after inverse-cone recursion | 23,122 |

The recursive depth distribution among accepted pairs is:

| Maximum inverse depth | Residue pairs |
| ---: | ---: |
| 0 (root already forbidden) | 16,384 |
| 1 | 9,984 |
| 2 | 6,568 |
| 3 | 4,088 |
| 4 | 1,900 |
| 5 | 514 |
| 6 | 68 |

Thus 23,122 residue cylinders are excluded only after following one or more inverse-parent levels; they are not consequences of the immediate forbidden-image test alone.

The census is computational evidence, not a Lean theorem asserting the total. The Lean theorem does formally certify every individual residue cylinder for which the checker returns true. The exact recurrence and census code are preserved in [probe.py](../im-results/agent42-modular-cone/probe.py).

## Concrete source-state exclusion beyond the old growth gate

For \(J=21,m=3\), the stopping equation gives
\[
k=2^8\cdot23-(21+9+4)=5854.
\]
The root residue modulo 256 is \((43,222)\). Its second coordinate is even, so the root is not in the immediate forbidden odd-image set. The inverse-cone checker accepts this residue, and the formal theorem high_stop_example_21_3 proves
\[
\neg\,\mathrm{CReach}(43,5854).
\]
This parameter is outside the earlier unified-index growth gate: \(21>3\cdot3+1\). In the original high-branch indexing, it corresponds to \(j=20,m=3\).

## Integration into the exact Machine C criterion

ModularConeHighStopCriterion.lean defines
\[
\mathrm{highAllowedModular}(j,m)
:=\mathrm{highAllowed}(j,m)\land
E_{b(j+1,m)}(j+1,m)=\mathrm{false},
\]
where \(j\) is the original high-branch index and \(J=j+1\) is the unified index.

The theorem BB6.Agent42ModularCone.blank_halts_iff_modular is an exact equivalence for the existing Machine C blank-halting criterion with this additional necessary high-stop filter. It preserves both directions of the equivalence. It does not bound the remaining existential parameters or decide Machine C.

## Reproducibility and proof boundary

- Generic checker and soundness proof: [ModularCone.lean](../im-results/agent42-modular-cone/ModularCone.lean).
- Original-source adapter: [ModularConeSource.lean](../im-results/agent42-modular-cone/ModularConeSource.lean).
- High-stop theorem and concrete example: [ModularConeHighStop.lean](../im-results/agent42-modular-cone/ModularConeHighStop.lean).
- Exact criterion integration: [ModularConeHighStopCriterion.lean](../im-results/agent42-modular-cone/ModularConeHighStopCriterion.lean).
- Exact finite probe: [probe.py](../im-results/agent42-modular-cone/probe.py).

The original-source theorem passed Lean 4.36.0-rc2 CI in [run 45355518699](https://github.com/FlareZ123/bb6/actions/runs/45355518699). The exact high-criterion integration passed in [run 45357876925](https://github.com/FlareZ123/bb6/actions/runs/45357876925). Both workflows include the repository's source-closure and sorryAx checks.

This result excludes a substantial, explicitly described set of infinite high-stop cylinders. It does not prove that every high-stop parameter is excluded, does not establish Machine C nonhalting, and does not determine the exact value of \(BB(6)\).
