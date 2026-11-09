# P1 inverse shadow: exact cost-level conservation and two-feeder complementation

**Mathematical statement (9 November 2026).** This dossier establishes an exact pointwise pairing between the two **abstract source-derived** P1 inverse feeder languages when paths are indexed by accumulated inverse **cost**, rather than generation. The proof is elementary binary-marker arithmetic; its central congruence and marker-complement identities have independently compiled in Lean 4.36.0-rc2 using standard axioms. The whole finite-word/actual-edge equivalence below is a paper proof checked by direct exact-integer enumeration. A second exact full-period comparison identifies the 1,213 cost-14-support residues modulo 4,096 with **the entire complement of the existing source-certified 2,883-residue necessary-gateway sieve**. This last identity is a finite arithmetic equality between two independently computed sets; it is not a new original-source nonhalting theorem. Original P1 blank-root nonhalting and BB(6) remain unresolved. External priority has not been assessed.

## Exact theorem

Let `N_s(C;q)` count finite, possibly branching **depth words with multiplicity**, of total cost `C` from the source-derived scalar feeder

- `s=8: L=16q+8, (m,z)=(0,12q+4)`;
- `s=9: L=16q+9, (m,z)=(0,10q+4)`.

An edge of depth `t>=0` is legal precisely when `2^t | z` and `L+m+t+z/2^t` is odd. It increments `m` by `t+1` and sets `z'=(L+m+t+z/2^t-1)/2`. These are the same abstract equations as [Agent 9's source-derived shadow](../agent9-p1-shadow/README.md) and [Agent 13's exact source budget library](../agent13-p1-adaptive-param/README.md). Count words independently even when their endpoint nodes coincide.

For every integer `q>=0`, every integer `M>=2`, set `P=2^(M-2)` and

```text
delta(M) = 0                  if M is even,
           2^(M-3)            if M is odd.
```

Then the **pointwise exact identity** is

```text
N_8(M;q) = N_9(M-1;q + delta(M)).
```

Both sides are periodic in `q` modulo `P`. For **even** `M`, the complete two feeder cost counts agree **at the same parameter q**, with one unit of cost offset; for odd `M`, the pairing translates `q` by half of the period. In particular, for every complete length-`P` interval of nonnegative `q` values,

```text
sum_q N_8(M;q) = P = sum_q N_9(M-1;q),
mean_q N_8(M;q) = mean_q N_9(M-1;q) = 1.
```

The identity also pairs the exact cost-level multiplicity histograms and all finite moments. It does not construct a single parameter-independent isomorphism of infinite inverse trees because the translation depends on `M`.

## Exact binary-marker proof

For a finite legal word, put `k_i=t_i+1>=1` and partial costs `s_j=k_1+...+k_j`, with total `C=s_r`. Encode its internal boundaries by the binary marker

```text
H = sum_j 2^(s_j-1).
```

The final bit at position `C-1` is always set, and the other `C-1` bits bijectively encode all positive compositions of `C`. The raw scalar edge equation `2^(t+1) z' = z + 2^t(L+m+t-1)` telescopes to

```text
2^C z_final = (c+16H) q + 4 + side*H + D,
D = sum_j 2^(s_j-1)*(s_j-2),
c=12 for side8; c=10 for side9.
```

Here `D` may contain a negative first summand but the displayed full numerator is nonnegative. Divisibility of this final numerator by `2^C` is equivalent to legality of **every** preceding edge: reduce the telescoped equation modulo `2^(s_j)` to recover each prefix-integrality condition. The quotient and parity requirements are equivalent to integral successor values, and all successor values are positive for `q>=0` and the stated feeders. Thus terminal integrality entails all prefix conditions, with no hidden synthetic-path assumption.

For side9 at cost `m=M-1`, define `h=m-1=M-2`, `P=2^h`, with internal bit choices `b_0,...,b_(h-1)` and fixed final bit at `h`. Define a nonnegative integer `X` by summing `W_i` over marked positions:

```text
W_0=4;       W_i = 2^(i-1)*(i+8), i>=1.
X=(9H+D)/2.
```

The all-prefix legality condition for the side9 word reduces exactly to

```text
P divides (5+8H)*q + 2+X.                   (9)
```

Map this composition to the side8 composition of total cost `M` by increasing its **first** part by one. Every marker position increases by one, so the side8 numerator condition becomes

```text
P divides (3+8H)*q + 1+X.                   (8)
```

For each `h>=1`, complement **all h internal binary marker bits**, leaving the terminal bit set. Call the new marker and score `Hc, Xc`. Their exact identities are

```text
H + Hc + 1 = 3P,
X + Xc + 3 = (3h+22)*(P/2).
```

The second identity follows by summing `W_0+...+W_(h-1)+3=(h+6)*2^(h-1)` and including both copies of the terminal score `W_h`. These equalities are independently proved by [CostMarkerDuality.lean](CostMarkerDuality.lean) without custom axioms.

In (8) write `a=3+8H`; in (9) for the complemented word write `b=5+8Hc`. Then `a+b=24P` and `b` is odd, with `b≡1 (mod 2)`. Taking `n=P/2` and `T=3h+22`, the sum of the two divisibility numerators after the translated parameter is a multiple of `P` exactly when the translation is `(T mod 2)*n`. Since `T mod 2=h mod 2`, this is the stated `delta(M)`. Thus (8) holds for the original marker if and only if (9) holds for the complemented marker at `q+delta(M)`. Bit complementation is a bijection, proving the pointwise count theorem. The remaining base `h=0` (M=2) has one legal word for each feeder.

Finally, each cost-`C` feeder word accepts a **single** residue class modulo `2^(C-2)` for side8 or `2^(C-1)` for side9, since the congruence has odd coefficient `3+8H` or `5+8H`. The number of candidate compositions equals the modulus. Summing each accepted residue with multiplicity proves the exact mean-one conservation law.

## Exact bridge to the current P1 source-certified gateway sieve

A direct comparison with the original-source certified lists establishes the following complete **finite set identity**, without an appeal to the numeric equality of counts alone:

```text
{q mod 4096 : N_8(14;q)>0}
= {q mod 4096 : N_9(13;q)>0}
= {0,...,4095} minus the union of the existing
  701/1024 and 79/4096 source-certified gateway classes.
```

The first equality is an instance of the **even-cost same-q theorem**. The last equality is a complete, exact comparison of the **actual 4096 residue values**, yielding exactly 1,213 supported residues and 2,883 certified-excluded residues. The source-certificate sets are extracted directly from the Lean source lists `DensityCount695.lean`, `DensityCount700.lean`, `QFinal.lean`, and the single late-start class q≡5 mod4096 from `Q4101.lean`. The matching 1,213-element set is computed *independently* from 4,096 one-residue binary-marker congruences and from 4,096 full scalar-grammar enumerations. The three sets match element for element, including their exact membership at every q.

[The executable full-set comparison](cost14_source_sieve_bridge.py) provides an auditable, deterministic witness for the complete equality. No statistical sampling, floating point arithmetic, heuristic pruning or numerical fitting is used.

**Interpretation and boundary.** The source-certified excluded classes apply to the particular P1 necessary critical-index gateway, with their original lower-parameter restrictions; the special new q≡5 class starts at q=4101. Therefore the finite set equality identifies the *exact asymptotic residue complement* of those certificates, giving a cost-14 shadow characterization of the previously unexplained 1213/4096 surviving congruence classes. It does not prove that a cost-14 shadow word makes the genuine blank root reach a critical state. Nor does nonexistence at cost 14 by itself exclude paths that jump over cost 14 in a single larger-depth edge. Global P1 halting, its other gateways and all-time exception handling remain open.

This correspondence is particularly useful as a next research selector: concentrate on root-connected exclusion of the cost-14-positive residue set, and clarify whether the existing source checker fails on those residues because of exactly the cost-14 frontier or because of other exceptional exits. The coincidence supplies a **precise boundary**, while a proof-carrying all-cost closure remains the missing task.

## Verification and scope

- [CostDualityCore.lean](CostDualityCore.lean) proves the *general congruence pairing* `algebraic_duality` for all natural `p,n,H,Hc,X,Xc,q,T` subject to the stated marker identities. Its `#print axioms` is `[propext, Quot.sound]`.
- [CostMarkerDuality.lean](CostMarkerDuality.lean) proves the binary marker sum, weighted marker sum, explicit prefix weight formula, and `cost_congruence_duality` for all Boolean internal-boundary words, all `q` and all positive `h`. Local Lean 4.36.0-rc2 compilation succeeded. Its complete theorem also has only `[propext, Quot.sound]` and no `sorry`. It proves the exact arithmetic-to-congruence transformation. The additional scalar recurrence-to-word-language induction in this note has **not** yet been embedded into Lean against the original P1 source.
- [cost14_source_sieve_bridge.py](cost14_source_sieve_bridge.py) compares all 4096 source-certified-class complements with all 4096 exact cost-14 marker congruences and independent raw scalar-grammar tests. The sets coincide exactly; this is a deterministic finite set identity, not a new original-source theorem.\n- [cost_duality_regression.py](cost_duality_regression.py) directly evaluates the original scalar legal-depth grammar via exact integers and memoization, independent of the marker formulas, for **all** `q mod P` and costs `M=2,...,12`; it checks the translation and mean-one statements. Further checks at five larger non-canonical parameters per cost passed locally. This is finite regression, never an all-cost proof.
- The local all-parameter proof above concerns the **source-derived scalar shadow**. The known one-directional source transport and bounded-cost source checks do not imply every abstract path lifts to an admissible authentic machine inverse step at arbitrary `q` and cost. No claim about any genuine blank-reachable odd cone follows merely from this pairing.

**Next mathematical task:** prove a cost-indexed *all-source* correspondence on the safely encoded feeder cone and determine why the 1213/4096 cost-14-positive classes resist current source certificates. Investigate a root-relevant all-cost obstruction that handles jumps over the cost-14 boundary and every exceptional source exit. The mean-one law alone allows concentrated collisions and implies no extinction or genuine machine nonhalting theorem.
