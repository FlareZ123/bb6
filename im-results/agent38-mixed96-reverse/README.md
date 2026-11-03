# Machine C mixed96: compact reverse cores and four terminal feeders

**Agent 38, 2026-11-03. Computational research artifact, awaiting Lean-kernel finite closure certification.** This is an alternative to Agent41's 260,672-reachable-state BFS certificate and 96 row-block generator. It uses Agent41's **already original-source CI-verified** mixed96 transition abstraction (CI [41680051185](https://github.com/FlareZ123/bb6/actions/runs/41680051185)); the new finite core assertions below have been exhaustively checked by an independent Python graph construction and have **not** yet been Lean certified. Machine C and BB(6) remain open. Do not promote this note to `results/` without independent checking and novelty review.

## Statement supported by exhaustive finite computation

For the mixed quotient `(a mod96, k mod96, c<2 ? c : 2+(c-2) mod48)` of the original [Agent11 Machine C accelerator](../agent11-c-line/CLine.lean), define the finite abstract graph by checking `nextC` at the 2×2×(1 or 2) representatives described in [Agent41's original dossier](../agent41-mixed96/README.md). There are **460,800 vertices and 3,575,808 representative edges** (including duplicates).

Two disjoint subsets, `CoreA` and `CoreB`, each have exactly **2,256 vertices**. Every abstract predecessor of a vertex in either core belongs to that same core. The projected true blank entry `(5,0,1)` belongs to neither. The cores are exactly the *shared* portions of the inverse-ancestor closures of the four listed targets.

For `c≥2` in the abstract domain `2≤c<50`, put
`x=(a-(c-2)) mod96`, `y=(k+(c-2)) mod96`.
The subtraction here is mathematical modular subtraction; it does **not** mean truncated natural subtraction.

### Core A

For `c=0`, include precisely the three residue cylinders `(a mod48,k mod24) ∈ {(18,23),(20,0),(42,11)}`. For `c=1`, use `{(18,22),(20,23),(42,10)}`.

For `c≥2`, include precisely the union of these six tests on `(x,y)`:

1. `x mod48=2` and `y mod24=5`;
2. `(x,y)=(12,29)` or `(60,77)`;
3. `x mod48=17` and `y mod24=21`;
4. `x mod48=19` and `y mod48 ∈ {0,22,46}`;
5. `x mod48=26` and `y mod24=17`;
6. `x mod48=41` and `y mod24=9`.

The exact abstract incoming vertices of each target form a forced two-step predecessor chain:
- `(13,31,0) ← (13,30,1) ← (13,28,3)` with last vertex in Core A;
- `(61,79,0) ← (61,78,1) ← (61,76,3)` with last vertex in Core A.

Thus the reverse ancestor set of either target is `CoreA ∪ {target, its c=1 feeder}`, cardinality **2,258**. The two targets' ancestor sets intersect in exactly Core A.

### Core B

For `c=0`, include `(a mod48,k mod24) ∈ {(4,16),(18,7),(42,19)}`. For `c=1`, use `{(4,15),(18,6),(42,18)}`.

For `c≥2`, use:

1. `x mod48=3` and `y mod24=14`;
2. `x mod48=10` and `y mod24=9`;
3. `x mod48=17` and `y mod24=5`;
4. `x mod48=19` and `y mod48=32`;
5. `(x,y)=(28,77)` or `(76,29)`;
6. `x mod48=34` and `y mod24=21`;
7. `x mod48=41` and `y mod24=17`.

Forced two-step predecessor chains:
- `(29,79,0) ← (29,78,1) ← (29,76,3)`, final vertex in Core B;
- `(77,31,0) ← (77,30,1) ← (77,28,3)`, final vertex in Core B.

For either target the exact reverse ancestor set is Core B plus the two low-c feeders, **2,258** vertices. Core A and Core B are disjoint.

## Reproduction and trust boundary

Run `python verify_reverse.py` using Python 3.10+ from this directory. The stand-alone checker transcribes the original `nextC` branch equations independently of Agent41's C++ source, constructs all 3,575,808 edges, evaluates the formulas at all 460,800 vertices, checks the absence of any edge into either core from outside, checks each feeder's **unique** abstract predecessors, computes the four complete reverse closures, and independently computes the previously reported forward census **260,672 reached / 2,022,544 reached edges**. All assertions must pass.

This yields a simple finite proof specification:
1. Source theorem: `BB6CLine.nextC` steps imply mixed96 abstract graph edges. Already proved in Agent41's unmodified-source CI.
2. **Missing kernel theorem:** For each of the two *computable residue formulas*, prove `abstractEdge u v → Core(v) → Core(u)` for all abstract vertices. Equivalently kernel-check the exhaustive finite loop, ideally with source-linked `#print axioms` audit. Existing Python assertions are valuable evidence, not a Lean theorem.
3. Prove the eight displayed unique immediate-predecessor properties (four targets and four c=1 feeders) by a similarly checked finite/semantic argument.
4. Combine these with `source_reachable_is_closed` for the complements, the initial exclusions, and [Agent41's already-Lean-checked stopping parameter arithmetic](../agent41-mixed96/SecondMod96.lean), then connect Agent15's original-source stopping criterion.

## Why this is a useful reduction

The 2256-state inverse core is described without a 260,672-state reachability bitset. The generic `a>0,c≥4` source branch `(a,k,c) ↦ (a-1,k+1,c-1)` preserves `x,y` exactly. Therefore a prospective symbolic inverse-closure proof could focus on exceptional `c=0,1,3` and `a=0,c≥4` branches and modular wraparound. This is a proposed proof strategy, **not** an existing formal proof.

Finite experiments show that enlarging Core A's special `(12,29)/(60,77)` high-c pair to a full independent Cartesian congruence cylinder, or enlarging the target's exceptional c=0/1 singleton to all lifts modulo48/24, makes the entire 460,800-state graph backward-reachable. Preserve exact pair coupling: careless formula simplification makes the closure useless.

**Unresolved:** Lean check of all finite edge implications and predecessor uniqueness; original-source halting bridge composition; external novelty and overlap with other modular exclusions; all-time status of Machine C, and exact BB(6).

## Direct all-natural-number inverse-closure proof (analytic reduction, 18:29 UTC)

The core formulas also define predicates on **unbounded real** source coordinates: for `c≥2`, take `x=(a-(c-2)) mod96`, `y=(k+(c-2)) mod96` using ordinary modular subtraction. For `c=0,1), apply exactly the low-c congruence families above. Because both high-c patterns are invariant under the simultaneous substitution `(x,y)↦(x+48,y+48) mod96`, the all-natural predicate agrees with the mixed quotient's predicate after projection. This uses only the directly inspectable residue formulas, not a BFS.

**Claim, with hand-checkable proof cases below:** For either `CoreX`, every actual `nextC(s)=some t` satisfies `CoreX(t) ⇒ CoreX(s)`. The claim has a finite arithmetic proof using the following complete case analysis. The scripted exhaustive verifier above independently checks its quotient consequence. A *Lean-kernel source-connected proof* of the case analysis is still outstanding.

Let `d=c-2` when `c≥2`. Every high-c member has `x+y` modulo 24 in one of these sets:

- Core A: `{2,7,14,17,19}`.
- Core B: `{3,7,9,10,17,19,22}`.

Thus **neither** high-c core has `x+y≡0,1,4 (mod24)` (and neither admits a multiple of 4). Cases from the exact source branch table:

* `c=2`: no successor.
* `c=1`: successor `(a,k+1,0)`; the low-c definitions were chosen as exact one-unit shifts, so membership of the successor implies membership of the parent.
* `c=3`: successor `(a,k+2,1)`. In Core A, the three possible low-c successor cylinders map to high classes A3, A4, A6 respectively via `x=a-1,y=k+1`. In Core B, they map to B1, B3, B7. This is immediate congruence arithmetic.
* `c=0,a=0`: successor `(1,0,2k+2)` has high-c `x+y≡1` and is therefore outside both cores.
* `c=0,a=1`: for `k=0`, successor `(5,0,1)` is outside the low-c sets; for `k=1`, successor `(2,2,1)` is outside; for `k≥2`, successor `(2,2,2k-1)` has high-c `x+y≡4` and is outside.
* `c=0,a≥2`: when `k=0`, successor `(a-2,1,1)` is outside both low-c sets. For `k≥1`, successor `(a-2,1,2k+1)` has `x≡a-2k-1 (mod96)` and `y≡2k (mod96)`. In Core A, the **only** high class with even y is A4: its conditions yield `(a mod48,k mod24)∈{(20,0),(42,11),(18,23)}`, exactly Core A at c0. In Core B, only B1 and B4 have even y: together they give `{(18,7),(42,19),(4,16)}`, exactly Core B at c0.
* `c≥4,a≥1`: successor `(a-1,k+1,c-1)` has **exactly the same** normalized `x,y` as the parent, so closure is immediate.
* `c=4,a=0,k even`: successor `(2k+2,2,1)` misses the low-c sets because its k-coordinate is 2. For `c≥5,a=0,k even`, successor `(2k+2,2,c-3)` has `x+y≡2k+4` divisible by 4; neither high core contains such a state.
* `c≥4,a=0,k odd`: successor `(2k+3,0,c)`, whose high normalized coordinates are `x'=2k+3-d,y'=d`; parent normalized coordinates are `x=-d,y=k+d`. A complete modular reduction leaves **three** possibilities per core:

| Core | Successor's high class | Necessary input congruences | Parent's high class |
|---|---|---|---|
| A | A2 special pair | `d%48=29, k%48=19` | A4 |
| A | A4, `y'%48=22` | `d%48=22, k%24=19` | A5 |
| A | A4, `y'%48=46` | `d%48=46, k%24=7` | A1 |
| B | B1, `d%48=14` | `d%48=14, k%24=7` | B6 |
| B | B1, `d%48=38` | `d%48=38, k%24=19` | B2 |
| B | B5 special pair | `d%48=29, k%48=3` | B4 |

All other classes force k even (contrary to this branch), a parity mismatch, or an impossible congruence. In particular the A4 possibility `d%48=0` forces `k%24=8` and the B4 possibility forces `k%24=0`, both even.

This exhausts the source cases, giving a short directly checkable invariant proof. The implication then excludes both cores for the genuine source orbit from `(5,0,1)`. The four low-c target cells have unique two-step predecessors inside the forbidden cores, as verified by direct branch inversion. **The exact mixed96 target exclusions therefore admit a human-sized modular proof**, subject to independent verification of the arithmetic and connection to the original source. This does not make any statement about all possible Machine C stopping targets or BB(6).

### Critical distinction

This is an **analytic proof draft**, with complete source-case coverage and separately checked finite evidence. It is stronger than an unstructured BFS claim, yet it is **not** a completed Lean theorem; do not advertise kernel certification or publishable external novelty until a validator checks both.

## Stronger odd-first-coordinate forbidden terminal cylinders (18:43 UTC)

The four displayed terminal targets are a small subset of the direct arithmetic-core consequence. For **every genuine original accelerated state** `(a,K,0)` with `K≥4`, exact inversion of the original `nextC` gives forced predecessors
`(a,K,0) ← (a,K-1,1) ← (a,K-3,3)`.
There are no other predecessors: the only source transition to `c=0` comes from `c=1`; at middle coordinate `K-1≥3`, the only source transition to `c=1` comes from `c=3`.

Consequently, if `coreA a (K-3) 3` or `coreB a (K-3) 3`, then `(a,K,0)` is never blank-reachable, **provided the core reverse-closure claim is proved**. In the finite mod96×96 torus, this covers **92** terminal cells, of which **36 have odd a** and are relevant to the second Machine C stopping locus. The odd-a cells have the following six *disjoint* explicit residue families:

| Candidate forbidden terminal residues `(a,K)` | Cells modulo96×96 |
|---|---:|
| `a%48=3, K%24=7` | 8 |
| `(a%96,K%96) ∈ {(13,31),(61,79)}` | 2 |
| `a%48=27, K%24=19` | 8 |
| `a%48=11, K%24=11` | 8 |
| `(a%96,K%96) ∈ {(29,79),(77,31)}` | 2 |
| `a%48=35, K%24=23` | 8 |

**Total: 36 distinct odd-a cells out of 9,216, requiring K≥4.** The count and all residue translations were independently recomputed in Python from the exact high-core formulas, with an explicit disjointness check. The other 56 of the 92 terminal cells have even a and do not directly intersect the known second stopping family of the form `a=2j+3`.

This exact two-step predecessor reduction is **new evidence of a potentially larger analytic exclusion mechanism**, but its full all-natural source theorem is still pending Lean validation. Further work must intersect these 36 odd-a cylinders with the Diophantine stopping equation `K+j+3m+5=2^(2m+2)*(j+3)` and check against prior certified P1/C filters before describing numerical novelty. This note does **not** claim original-Machine-C or BB(6) nonhalting.
