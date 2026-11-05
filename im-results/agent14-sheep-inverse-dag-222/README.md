# 222 all-exponent closed inverse DAG families for Sheep's genuine first-even graph

Agent 14, 2026-11-05. **Intermediate all-parameter mathematical theorem with exact executable certificate.** It uses the existing pinned-original-machine-certified first-even Sheep section equations and inverse case splitter. The complete new 222-family statement has **not** been imported into a single pinned-original-Cryptids Lean proof. No whole Sheep machine or BB(6) upper bound is claimed.

## Result

Fix P=122472. Among the 567 candidate exponent roots `j=648+216t+Pk`, where `0≤t<567` and `k≥0`, there are **222** distinct residue classes for which the exact complete symbolic E predecessor graph is finite and backward closed. Thus for every root in these 222 infinite families, genuine blank-even `EvenReach(10,2^j)` is false.

- **174** classes have **no incoming even-section edge**, previously documented with exact full-period certificate in [root-free 174](../agent14-sheep-root-free-174/README.md).
- **48** further classes have at least one symbolic predecessor but their full finite inverse graphs close after at most two inverse steps, with at most **three** nodes including the root. This improves the preceding combined coverage of 181/P (174 root-free plus sevenfold-tightened 648 family) by **41 additional classes**.
- The final arithmetic density of these new E exponent indices is **222/122472=37/20412**. It is an arithmetic exponent-index density, without halting-probability interpretation.
- The SHA256 of the comma-separated sorted 222 residue indices modulo P is `4e798268a891839c52a22d15db7934d1e20d072643e04fcd8fc5e9d59001c211`.

The 48 nonempty-DAG root representatives J are:

```
648, 6912, 8424, 10152, 11448, 15984, 18144, 20520,
22032, 25056, 27648, 31104, 33480, 34128, 35640, 38664,
45144, 47736, 49248, 50976, 52272, 53136, 61344, 62640,
62856, 65880, 68472, 70632, 71928, 74952, 79488, 80136,
85968, 88128, 88560, 90072, 93096, 97632, 102168, 103464,
103680, 105624, 106704, 112752, 115128, 115776, 120312, 120960
```

The full new nonempty-DAG graphs use only four symbolic inverse-node families in addition to the root, always represented as `N=(2^(j+s)+b)/d`:

```
Root R=(0,0,1)
X=(8,-1228,2187)        root edge (h=5,a=2)
Z=(10,-16576,3483)      root edge (h=3,a=6)
W=(7,-452,729)          root edge (h=4,a=2)
T=(13,-174404,31347)    child of Z, with exact edge from Z
```

There are **six distinct graph shapes**, with frequencies 24,12,6,3,2,1 in descending order. Three roots `15984,35640,97632` each have two immediate predecessors; three roots `31104,71928,112752` have a chain of two inverse edges ending at T. All other 42 nontrivial roots have a single parent with no parent itself. The complete checker constructs the actual exact rational-offset nodes from the original generic source equation; the displayed symbolic edges are a *sound necessary-predecessor superset* and need not be separately shown to be realizable.

## All-k completeness and why the finite DAG is rigorous

Every even incoming E edge has either the generic odd-part-v≥5 source equation or the odd-part-three exceptional equation, certified in the original Sheep machine source module `SheepEvenSourceAlgebra.lean`. For a symbolic target node `Y=(2^(j+s)+b)/d`, with even b and odd d>0, a hidden odd-return valuation h has

```
D=d*3^h, C=D+2^h*(b-d), K(a)=D*(2*a-1)-2*C,
M(a)=D*(2^(a+1)+1)
```

and the generic source must satisfy `2^(j+s+h+1)=K(a) mod M(a)`. For each node, the checker proves that Y(j) is a positive integer even above the genuine seed 10 for all k, by checking exact base divisibility and the modular period `2^P=1 mod d`. It establishes a **uniform bound h<H**, where `H=v3(Y(J)-1)+1`, by verifying `2^P=1 mod d*3^H` and that the base numerator is nonzero modulo that same modulus. Roots with nonuniform h are explicitly excluded from certification.

For every h<H, the standard strictly-growing odd-remainder gap proves all generic 2-adic source valuations a≥A impossible, where a finite checked A has `1<K(A)<2^A`, K odd, and `2^A≥2D`. The exhaustive low-a exact modular test uses `o=ord_M(2)` and `q=o/gcd(o,P)`, and checks every residue `0≤t<q`. A row with no match excludes that source valuation for all k. A row with matches on **every** residue yields the exact symbolic child node via the original source algebra:

```
s'=s+h+a+1,
b'=2^(a+h+1)*(b-d)+2^a*d*3^h*(3-2*a),
d'=d*3^h*(2^(a+1)+1).
```

A *partially matching* row prevents certification of that root. Every special odd-part-three source is excluded by the same exact exponential gap and its verified base inequalities as in the earlier seven-cone result. For a successfully closed graph, all possible genuine parents of every listed node lie at strictly greater graph depth, every leaf has no parents, and all node values stay distinct for every j in the progression. Distinctness is checked using the sign of the affine difference `(2^s_i*d_j-2^s_j*d_i)*2^j + (b_i*d_j-b_j*d_i)` and exact agreement of signs at j=J. A genuine path from the initial seed 10 would then have a last edge into a graph node, and iterative inverse descent would force an incoming edge into a leaf. That contradicts completeness.

## Reproduction and classification boundary

The standalone **Python 3 standard-library** certificate is available as invocation artifact `sheep_inverse_dag_222.py`, SHA256 `bc0e71694c918855aabce38980a54607100946c89b39058ec642fbfc158a0382`. It needs no input files or external library. It verifies and caches all **106** distinct multiplicative orders of 2 by direct modular iteration, checks the exact 222-class SHA256, reconstructs all symbolic DAGs, verifies all node divisibility/positivity/distinctness, and independently checks overlap against the 16 earlier comparable E families and the 133 root-free and sevenfold-tightened 648 progressions.

Among all 567 candidate j classes, the checker reports 294 roots with no partially matching root row and seven with nonuniform hidden valuations. The remaining 266 have partial congruence matches and are **unclassified**. Among the 294 complete root rows, 174 have no parent; 48 have closed finite DAGs; 72 have a child that remains unresolved within this algorithm because of partial or nonuniform inverse cases. Thus the certificate proves 222 families, leaving **345 candidate classes** unclassified in this fixed period, and infinitely many exponents elsewhere. The exact BB(6) value remains an open problem.

## Formal integration and future work

The local Lean 4.36.0-rc2 compilation of the fully source-shaped first family `j=1080+13608k` passed without admitted axioms, as documented in [ROOT1080-LEAN.md](../agent14-sheep-root-free-133/ROOT1080-LEAN.md). The original source inverse splitter and finite DAG soundness rule passed a pinned-original-Cryptids workflow in prior work. Kernel-certifying this entire 222-class certificate, then finding a true-root reachability invariant that covers the unbounded surviving families, would make progress toward closing the Sheep holdout. Merely continuing finite modular residue enumeration is unlikely to decide BB(6) alone.