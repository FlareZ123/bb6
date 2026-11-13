# Haar survival bounds for the P1 dyadic shadow tree

**Status:** intermediate result for the abstract two-counter P1 inverse shadow only. It does not establish an original-machine inverse path, decide P1, or determine BB(6).

## Statement

For feeder label s in {8,9}, let E(s,d) be the set of 2-adic parameters q for which at least one legal shadow word of length d exists, with no bound on its edge depths. The shadow recurrence and root states are:

- s=8 starts at (m,z)=(0,12q+4);
- s=9 starts at (m,z)=(0,10q+4);
- an edge of depth t is legal when 2^t divides z and s+m+t+z/2^t is odd;
- its child is (m+t+1,(16q+s+m+t+z/2^t-1)/2).

The depth-2 and depth-3 survival measures are exact and equal for both feeders:
\[
\mu(E(s,2))=3/4,\qquad \mu(E(s,3))=1/2.
\]
At depth 3 the common set is exactly q=1 or 2 modulo 4.

For depths 4 through 7, the following are rigorous lower and upper bounds. The lower endpoint is the exact measure of a finite union of dyadic cylinders; the upper endpoint adds an explicit bound for all omitted high-depth parent words.

| Depth d | Feeder s | Parent cutoff T | Enumerated parent words | Lower bound | Upper bound |
|---:|---:|---:|---:|---:|---:|
| 4 | 8 | 24 | 15,000 | 493/1024 | 2019329/4194304 |
| 4 | 9 | 24 | 15,625 | 247/512 | 8093699/16777216 |
| 5 | 8 | 18 | 123,462 | 903/2048 | 115589/262144 |
| 5 | 9 | 18 | 130,321 | 57983/131072 | 57985/131072 |
| 6 | 8 | 14 | 708,750 | 12781/32768 | 12793/32768 |
| 6 | 9 | 14 | 759,375 | 26906311/67108864 | 26926791/67108864 |
| 7 | 8 | 10 | 1,610,510 | 23273201/67108864 | 23731953/67108864 |
| 7 | 9 | 10 | 1,771,561 | 3027538197/8589934592 | 3077869845/8589934592 |

These intervals are for the unrestricted shadow tree, not merely the tree truncated at T. High-depth edges in the final generation are handled exactly; the cutoff applies only to the first d-1 edges.

## Why the final generation is exact

At a parent node, write the affine shadow coordinate on its cylinder as z=a+b r, where b is odd and r is the residual 2-adic parameter. For nonzero z let v=v2(z). If a 2-adic parameter gives z=0, every t of one parity is legal, so this singleton is not a failure case; for ordinary nonnegative integer q, z>0 follows from the offset invariant. Let C=(s+m) mod 2. For nonzero z, the number B of legal children is determined by

- C=0: B(2k)=k+1 and B(2k+1)=k;
- C=1: B(2k)=k and B(2k+1)=k+2.

Here the argument of B is v. Thus a node has no child exactly in one of two cases:

- C=0 and v=1, equivalently z=2 modulo 4;
- C=1 and v=0, equivalently z is odd.

Since b is odd, each failure condition selects exactly one residue of r. If C=0, the failure cylinder is the unique r modulo 4 satisfying
\[
r=(2-a)b^{-1}\pmod 4.
\]
The parent cylinder minus that one quarter-cylinder is the union of the other three quarter-cylinders. If C=1, the failure cylinder is the unique r modulo 2 satisfying
\[
r=(1-a)b^{-1}\pmod 2,
\]
and the parent cylinder minus it is the other half-cylinder.

Consequently, for every depth-(d-1) parent word, the full set of parameters for which that node has at least one child is a finite union of one or three dyadic cylinders. Taking the union over all parent words gives E(s,d), without imposing any cutoff on the last edge.

The local failure characterization and the unique affine failure residues are also kernel-checked in [ShadowSurvivalCore.lean](ShadowSurvivalCore.lean). It proves that type 0 has no legal depth exactly when z=2 modulo 4, type 1 has no legal depth exactly when z is odd, and that an odd-slope affine coordinate a+b r selects exactly one failing residue modulo 4 or 2. The Lean 4.36.0-rc2 axiom audit reports only standard axioms [propext, Classical.choice, Quot.sound], with no sorryAx. This module certifies the local cylinder rule, not the global tail or density argument.

## Rigorous tail bound for the parent cutoff

The finite calculation enumerates only parent words whose first d-1 edge depths are at most T. Every such parent contributes its exact full child-existence region as described above.

For omitted parent words, use exact first-moment conservation.

- At the s=8 root, the total cylinder mass of root edges with t>T is 2^(1-T).
- At the s=9 root, the corresponding mass is 2^(-T).
- At any later odd-slope node, the child cylinder for depth t has relative mass 2^(-t-1). Hence the total relative mass of children with t>T is
  \[
  \sum_{t=T+1}^{\infty}2^{-t-1}=2^{-T-1}.
  \]
- The sum of parent-cylinder masses at any generation is exactly 2, by the established first-moment theorem. Therefore, at each later parent-edge position, the total omitted mass is at most 2·2^(-T-1)=2^(-T).

There are d-2 non-root edge positions among the first d-1 edges. By a union bound, the omitted contribution to E(s,d) is at most

\[
\mu(E(8,d))-\mu(E_T(8,d))\le d\,2^{-T},
\]
\[
\mu(E(9,d))-\mu(E_T(9,d))\le (d-1)\,2^{-T},
\]

where E_T is the finite union computed from parent words with all first d-1 depths at most T. This proves every upper endpoint in the table.

For ordinary integers q≤Q, every actual edge depth satisfies t≤log2(z) because z is a positive integer divisible by 2^t. The offset invariant gives z≤L+m, and therefore m'=m+t+1≤2m+L+1 (using log2(L+m)≤L+m). For fixed d and q≤Q, this recurrence bounds every parent cost by O_d(Q), hence every parent depth by O_d(log Q). Only O_d((log Q)^(d-1)) distinct parent words can therefore occur among q≤Q. Counting each omitted cylinder contributes at most Q times its Haar mass plus one; the total additive overhead is o(Q). The same tail bound consequently controls upper natural density, not just Haar measure. Since each finite-cutoff union is periodic, squeezing its density between the lower approximation and the tail-corrected upper approximation, then letting T tend to infinity, proves that the natural density of nonnegative integer q admitting a depth-d shadow word exists and equals the Haar measure \mu(E(s,d)). The table therefore also bounds those natural densities.

## Reproduction

Run python3 generation_survival_census.py from this directory. It uses only the Python standard library and imports the exact affine cylinder constructors from finite_cylinder_regression.py. It enumerates parent words recursively, encodes cylinders by their dyadic prefix, removes cylinders already covered by a shorter prefix, and asserts the exact lower and upper fractions shown above.

The exact arithmetic in this invocation was evaluated independently with arbitrary-precision integer arithmetic. The Python reproducer is committed so future runs can reproduce the census directly.

## Interpretation and limits

The survival bounds decrease from the exact depth-3 value 1/2 to upper bounds below 0.36 at depth 7. This is evidence about the finite-generation geometry of the abstract shadow tree, not an asymptotic extinction theorem. The limit of \mu(E(s,d)) as d tends to infinity remains undetermined; no positive-measure or measure-zero infinite-path conclusion is claimed.

Even a proof that the abstract infinite-path set has Haar measure zero would not decide the original P1 machine: it would leave every exceptional integer parameter, and the source-to-shadow correspondence in the repository is still one-way. The converse source lift is being investigated separately. No BB(6) bound or exact value follows from this census.
