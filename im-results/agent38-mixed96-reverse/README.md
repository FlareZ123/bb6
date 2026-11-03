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
