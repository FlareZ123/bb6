# A source-certified modular inverse-cone sieve for Machine C's low stopping family

## Result

For the unified low stopping family \(J=0\), the source target is
\[
x=1,\qquad k+3m+4=2^{2m+3}.
\]
The modular checker is applied to
\[
(1,-3m-4)\pmod {2^b},
\qquad b_L(m)=\min(32,2m+1).
\]

The original-source Lean theorem
BB6.Agent42ModularCone.low_stop_excluded proves
\[
E_{b_L(m)}(0,m)=\mathrm{true}
\quad\Longrightarrow\quad
\neg\,\mathrm{CReach}(1,k)
\]
for every \(k\) satisfying the low stopping equation. The proof uses the original Machine C parent and forbidden-image laws through the generic source-cylinder exclusion theorem.

The fixed eight-bit specialization low_stop_excluded8 applies for \(m\ge4\). Since its predicate depends only on the residue modulo 256, every accepted residue class gives an infinite family of compatible low-stop parameters after taking sufficiently large lifts.

## Exact eight-bit census

An exhaustive evaluation over all 256 low-stop residues gives:

| Quantity | Count |
| --- | ---: |
| Accepted low-stop residue classes | 163 / 256 |
| Accepted immediately by the root forbidden-image test | 64 |
| Accepted only after inverse-cone recursion | 99 |

The recursive depth distribution is:

| Maximum inverse depth | Residue classes |
| ---: | ---: |
| 0 (root already forbidden) | 64 |
| 1 | 48 |
| 2 | 26 |
| 3 | 14 |
| 4 | 8 |
| 5 | 3 |

The census is computational evidence, not a Lean theorem asserting the total count. The formal theorem certifies each individual residue class accepted by the checker. The exact recurrence and enumeration are in [probe.py](../im-results/agent42-modular-cone/probe.py).

## Concrete non-immediate source exclusion

For \(m=11\), the stopping equation gives
\[
k=2^{25}-(33+4)=33,554,395.
\]
The root residue modulo 256 is \((1,219)\). Although its second coordinate is odd, the coordinate sum is \(220\equiv0\pmod4\), so the root is not in the immediate forbidden-image set. The inverse-cone checker nevertheless accepts the residue, and the formal theorem low_stop_example_11 proves
\[
\neg\,\mathrm{CReach}(1,33,554,395).
\]

## Adaptive finite probe

With the 32-bit cap, the low family accepts 883 of the 1,024 parameters \(m\in[0,1023]\). The unresolved parameters below 100 are
\[
0,2,6,8,10,15,16,22,27,32,34,43,47,72,74,82,86,91,98.
\]
This is a finite computational sample, not a universal statement about all \(m\).

## Reproducibility and proof boundary

- Generic checker and soundness proof: [ModularCone.lean](../im-results/agent42-modular-cone/ModularCone.lean).
- Original-source adapter: [ModularConeSource.lean](../im-results/agent42-modular-cone/ModularConeSource.lean).
- Low-stop theorem and example: [ModularConeLowStop.lean](../im-results/agent42-modular-cone/ModularConeLowStop.lean).
- Exact finite probe: [probe.py](../im-results/agent42-modular-cone/probe.py).

The low-stop module compiled in the source-closure validation preceding the later full-criterion proof failure; a dedicated low-stop CI run, 45364029622, is in progress. This result excludes a substantial family of infinite low-stop cylinders. It does not prove that every low-stop parameter is excluded, does not establish Machine C nonhalting, and does not determine \(BB(6)\).
