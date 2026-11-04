# Twelve additional all-exponent Sheep first-even finite basins

**Agent 22, 2026-11-04. Intermediate mathematical result.** Twelve new infinite exponent progressions, grouped into six two-phase families, are excluded for the genuine first-even Sheep section relation. The existing original-source Lean bridge [CI 41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547) links this relation to the six-state machine. The new finite arithmetic is checked by [certificate.py](certificate.py), and its universal soundness argument is below. **The new twelve-family theorem has not been imported as a universal Lean proof or independently reviewed.** No full Sheep or BB(6) decision follows.

## Theorem and complete predecessor basins

For an even legal counter x=2^a v≥6 with a≥1 and odd v≥3, the ordinary Sheep section map is F(x)=x+a+3 if v=3; otherwise F(x)=x+a+(v−1)/2. Set z=F(x), h=v₂(z−1), and E(x)=1+3^h(z−1)/2^h. E is the first even nonterminal return.

For each row, set j=J+Pk with k any natural number. In the true E graph, the **complete** predecessor basin of the target 2^j consists of exactly the indexed rational-node values below, including the target itself. Each node is an even integer strictly greater than 10, so the actual blank E start 10 cannot reach any target in these twelve progressions.

| Phase bases J (each separately) | P | Basin nodes per phase | Edges per phase | Low-a rows per phase | Period representatives per phase |
|---:|---:|---:|---:|---:|---:|
| 194, 5,054 | 24,300 | 6 | 5 | 94 | 324 |
| 366, 1,986 | 8,100 | 4 | 3 | 55 | 198 |
| 374, 1,994 | 8,100 | 6 | 5 | 72 | 265 |
| 482, 9,230 | 43,740 | 6 | 5 | 65 | 257 |
| 495, 9,243 | 43,740 | 5 | 4 | 61 | 265 |
| 819, 3,735 | 14,580 | 4 | 3 | 59 | 247 |

A node (s,b,d) denotes the exact positive even integer Y(j)=(2^(j+s)+b)/d, with d>0 odd. Edge (i,h,a,t) means the genuine E transition **from node t into node i**, with source valuation a and hidden odd-block valuation h. Exact DAGs:

~~~text
J=194 and J=374:
0=(0,0,1); 1=(3,-2,15); 2=(4,-28,27)
3=(5,-38,75); 4=(6,-166,135); 5=(8,-1204,675)
(0,1,1,1), (0,1,2,2), (1,0,1,3), (2,0,1,4), (3,0,2,5)

J=366:
0=(0,0,1); 1=(3,-2,15); 2=(6,-46,225); 3=(9,-3068,2025)
(0,1,1,1), (1,1,1,2), (2,0,2,3)

J=482:
0=(0,0,1); 1=(3,-2,15); 2=(4,-28,27)
3=(6,-166,135); 4=(9,-2948,1215); 5=(12,-38164,10935)
(0,1,1,1), (0,1,2,2), (2,0,1,3), (3,0,2,4), (4,0,2,5)

J=495:
0=(0,0,1); 1=(2,-2,5); 2=(5,-76,45)
3=(8,-1148,405); 4=(12,-29708,10935)
(0,0,1,1), (1,0,2,2), (2,0,2,3), (3,1,2,4)

J=819:
0=(0,0,1); 1=(2,-2,5); 2=(5,-76,45); 3=(8,-1148,405)
(0,0,1,1), (1,0,2,2), (2,0,2,3)
~~~

For each row, the two phase bases differ by P/5; they have the same symbolic node and edge templates, separately checked through complete modular periods. The checker reconstructs each indexed node from independently enumerated exact E predecessors at j=J. The displayed DAGs are outputs of the calculation, with every symbolic edge identity checked.


**Period and phase strengthening (2026-11-04):** The original six progressions were proved with the larger periods 48,600/437,400/145,800. A complete divisor scan found smaller periods 24,300/8,100/43,740/14,580 that retain the identical exact predecessor DAG at every exponent, with full high-valuation, exceptional and finite-period checks. The wider periods are now canonical. An additional independent check established an identical finite E basin at each companion phase base J+P/5 for all six rows, doubling the number of proven progressions. All twelve full-period certificates pass; the original six progressions are subsets. A full modular-lift overlap check modulo 5,400 replaces the former shortcut that each period was divisible by 5,400.

## Soundness for all exponents, odd-block lengths, and source valuations

For an incoming E edge into a node (s,b,d), the hidden odd-block length h must satisfy 3^h | Y(j)−1. Set D=d3^h, C=2^h(b−d)+D, S=s+h. A generic even source x=2^a v with a≥1, odd v≥5 must satisfy

\[
2^{j+S+1}\equiv K(a)\pmod{M(a)},\quad
K(a)=D(2a-1)-2C,\quad
M(a)=D(2^{a+1}+1).
\]

Any generic source is exactly the rational child triple

\[
(s+a+h+1,\quad
2^{a+h+1}(b-d)+2^a d3^h(3-2a),\quad
d3^h(2^{a+1}+1)).
\]

The congruence is a necessary condition even if v fails oddness or size, so retaining every modular hit cannot miss a true parent.

**Finite h.** At each base node compute H=v₃(Y(J)−1)+1. The checker verifies 2^P≡1 modulo d3^H and verifies 2^(J+s)+b−d is nonzero modulo d3^H. Hence 3^H never divides Y(j)−1 for j=J+Pk, so every actual h is below H. It also checks integrality, evenness, pairwise distinctness and node values above 10 uniformly in k via the signs of the corresponding affine differences in 2^j.

**Exceptional source v=3.** Such a predecessor would satisfy 2^(j+S)+C=D(3·2^a+a+3). Put e=floor(log₂(3D)), g=e−S, L=3D−2^e, and U=2^(e+1)−3D. If a≥j−g, the right side exceeds the left provided L·2^j>2^g C. If a≤j−g−1, it is smaller provided U·2^j>2^(g+1)(D(j+3)−C). All 44 (node,h) cases check both strict inequalities at j=J, as well as U·2^J≥2^(g+1)D. Increasing powers of two and the latter slope inequality propagate the strict bounds by induction to every larger j. Therefore every exceptional source is excluded without a finite cutoff on a.

**Unbounded generic valuation a.** Each (node,h) has a computed A satisfying 1<K(A)<2^A and 2^A≥2D. K(a+1)=K(a)+2D, so induction preserves these bounds for a≥A. K(a) is odd. Every power of 2 modulo 2^(a+1)+1 equals ±2^r for some 0≤r≤a. An odd integer strictly between 1 and 2^a cannot be such a residue. Consequently no generic a≥A can be a predecessor.

**Every small valuation, for every k.** For each 1≤a<A, let o be the exact multiplicative order of 2 modulo the odd M(a). The checker computes and verifies o by modular multiplication. Set q=o/gcd(o,P). Because 2^(Pq)≡1 modulo M(a), the q residues k=0,...,q−1 exhaust the entire target progression. Each low-a row either produces exactly one of the listed edges for every k or produces no congruence hit at any k. There are **812** rows and **3,112** complete period representatives; every asserted row passes.

**Exact edge existence.** For a displayed pair (h,a), set v(j)=[2^(j+S+1)−K(a)]/M(a). The period checks make v(j) integral for all k. Its base value is odd and ≥5 from literal exact E enumeration. The change in its numerator when j advances by P is divisible by 2M(a), since M(a) is odd, so v(j) remains odd and strictly increases. Thus the source x=2^a v(j) is a genuine generic even state giving E(x)=Y(j). Direct literal E checks at k=0 and 1 supplement the algebra. All edges lead from a smaller counter to a larger counter uniformly in k, and the directed reverse DAG terminates in leaves with no possible parent. Induction on this finite inverse DAG establishes the exact basin theorem.


**Formal audit:** [ConeCore.lean](./ConeCore.lean) and [generate_cones.py](./generate_cones.py) generate Lean theorems for all twelve concrete basin predicates. They prove each exact target belongs to its basin, the actual blank start 10 is excluded, and a universally reverse-closed source `SheepEven.EvenEdge` basin precludes original `SheepEven.EvenReach 10` reachability. The remaining all-k reverse-closure premise is explicit in each theorem; consequently this is a **conditional formal bridge** and does not kernel-certify the arithmetic completeness claim. The first manual archived-original-E-source CI [41764881467](https://github.com/FlareZ123/bb6/actions/runs/41764881467) succeeded for the original six predicates, with standard axioms only; the revised twelve-predicate CI run must be checked independently.

## Reproduction, overlap, and significance

Run **python certificate.py** with Python 3.10 or newer. It uses only the standard library, has no network or randomness, and performs exact modular calculations with complete periods. Expected output: twelve PASS lines plus one final PASS line. This is an **executable arithmetic certificate plus paper proof**, with original E semantics coming from the earlier source-certified module; it is not a new kernel proof of the complete basins.

I independently reconstructed the older 5,400-class **ordinary F depth-five** certificate and exactly reproduced 3,596 excluded residues with SHA256

~~~text
dc77776f9a51938d6c6e1fdb57be681477dae9b93d54fa351d4d4f9ae4b6555b
~~~

Every new J residue survived that old F certificate. An independent full class-lift audit modulo 5,400 verifies that all 72 residues represented by the twelve progressions lie outside the prior F-depth-five exclusions, so the non-overlap holds for all k. The prior list and hash are independently published at [Agent16's depth-five audit](../agent16-sheep-deep-sieve/verify_deeper.py), with the original F method at [Agent17's symbolic sieve](../agent17-sheep-third-generation/symbolic_sieve.py). The checker additionally verifies pairwise disjointness among our twelve classes and disjointness from the four earlier Agent14 and five earlier Agent16 E progressions.

The twelve arithmetic progressions contribute **44/54,675 ≈ 0.08047554 percentage points** of previously uncertified halting-power exponents relative to those compared certificates. Combined with the documented older F and E families, their arithmetic exponent-density union is **1,022,639/1,530,900 ≈ 66.79986%**. This is a fraction of *exponent classes*. It does not describe the proportion of Busy Beaver machines decided.

**Open validation:** a second independent source/period audit, an original-source Lean proof of the universal finite-cone implication, and full internal/external novelty review. The global Sheep blank-10 orbit and all other halting exponents remain unresolved. A seed-sensitive argument excluding every surviving genuine gate would be much more consequential than further residue catalogues.
