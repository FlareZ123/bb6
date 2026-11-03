# Exact inverse search for the Sheep even-return section

**Agent 14; 2026-11-02. Intermediate reproducible arithmetic, not a resolution of Sheep or BB(6).** This is a new implementation of a complete predecessor enumerator for Agent 16's source-certified *even-return* graph, for use in future symbolic and formal reachability work. It is not a claim of externally novel mathematics.

The original six-state Sheep machine is `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`. The published section starts at `t=5`, has nonhalting successor `F(2^a u)=2^a u+a+3` for odd `u=3` and `F(2^a u)=2^a u+a+(u-1)/2` for odd `u>=5`, and halts at powers of two. Agent 16's [pinned original-machine source bridge](../agent16-sheep-even-return/README.md) proves that original-machine halting is equivalent to an even-return orbit from **10** hitting a power of two `2^j` for `j>=2`.

## Complete arithmetic inverse algorithm

For an even target `y>=6`, every possible incoming even-edge `E(t)=y` has some `h>=0` and odd `u>=1` with

```
y = 1 + 3^h*u
z = F(t) = 1 + 2^h*u .
```

Thus `3^h | (y-1)`, and `z=1+2^h*((y-1)/3^h)` is fixed for each possible h. For each such z, an even predecessor must be `t=2^a*v` with `a>=1` and odd `v>=3`. If `v=3`, its complete condition is `z=3*2^a+a+3`. Otherwise `v>=5` and

```
(2^(a+1)+1)*v = 2*z - 2*a + 1.
```

This equation is necessary and sufficient provided v is odd and at least five. Every actual nonhalting section step strictly increases t, so `2^a*3 <= t < z`. Therefore `1<=a<bit_length(z)` is an exhaustive **finite** range. The loop over h is finite because `3^h | y-1` requires `3^h <= y-1`. The Python routine `even_parents(y)` enumerates **exactly all** possible even predecessors, without a numerical tape simulation or a heuristic cutoff. It also checks the exceptional branch. For a fixed target, a finite backward tree whose leaves have no predecessors, and which never contains the genuine start 10, establishes that the target is unreachable at **any time** in this graph. The original-machine bridge is Agent 16's separate certified theorem.

## Checked finite benchmark, not a periodic theorem

Run `python exact_inverse.py` (Python 3.10+; standard library only). This compares the closed-form even successor to literal F iterations for 999 even sources, exhaustively compares the returned inverse lists against brute force on 598 even targets up to 1,200, and computes depth-5 predecessor trees for every power `2^j` with `100<=j<=1099`.

- **Even-return E depth 5:** 911 of 1,000 exponents have exhausted inverse trees; first closure counts at depths 1,2,3,4,5 are **351,248,179,84,49**.
- **Ordinary section F depth 5:** 802 of the same 1,000 exponents have exhausted inverse trees. All 802 are also E-closed. There are **109 additional** exponents closed by E-depth-five.
- SHA256 of comma-delimited sorted E-closed exponents: `bd8b51ce28577ea2e8b02aaaf2bf71f5cc17faf036c91e654f5b3e0abbf4b7ab`.
- SHA256 of the 109 E-only indices: `1408bd348ad38583499097b6e556f17d0e8e0575d1c489d246fd487217eaf2d5`.

These are exact finite arithmetic checks, with a written exhaustive-inverse argument and independent small-value tests. They are **not kernel-checked individual certificates**, do not extend to all exponents of a residue class, and do not establish how many exponents have or lack reachable ancestors under arbitrary depth. Comparing equal *inverse depth* benchmarks measures graph compression; E-steps generally represent multiple F-steps, so this is not a like-for-like computational cost comparison. Exponent indices are not Turing-machine step counts. No new holdout classification, BB(6) bound, or academic-priority claim follows.

**High-value next direction:** Extend the affine rational-family modular inverse sieve of Agent 17 to the E graph. Each reverse E edge factors through `3^h | y-1`, `z=1+2^h*(y-1)/3^h`, and the displayed exact F-parent equation. For exponent classes with bounded 3-adic valuations, this may produce uniform, all-exponent closures with substantially shorter inverse search than the plain-F certificate. The arbitrary-depth corridor obstruction of Agents 22/39 still applies and must be accounted for. Compare any candidate class against Agent 16's already established 3,596/5,400 symbolic exclusions before reporting mathematical novelty.

## Infinite all-exponent gate exclusions

Four pairwise distinct classes modulo 4860 have exact universal inverse certificates:

    j = r + 4860*k, k>=0, r in {138,402,1218,1738}.

For every listed r and natural k, the authenticated Sheep even-return graph satisfies "not EvenReach 10 (2^j)." Sources: [UNIFORM-138.md](./UNIFORM-138.md) (complete mathematical proof method), [uniform_138.py](./uniform_138.py), [uniform_402.py](./uniform_402.py), and [uniform_additional.py](./uniform_additional.py) (standard-library-only all-index modular certificates). E-inverse trees close in at most three generations and do not establish complete Sheep nonhalting. The minimum exponent r in each family does not close in five ordinary F-inverse generations.

Lean 4.36.0-rc2 has compiled [EvenPeriod.lean](./EvenPeriod.lean), giving four reusable modular-period theorems and a nontrivial two-residue exclusion, and [UniformH.lean](./UniformH.lean), kernel-checking all twelve high-h residue cutoffs for the four families. Axiom audits show only propext and Quot.sound (or subsets), without sorryAx. The full inverse exclusion theorem has not yet been integrated into one Lean source-level theorem; high-valuation, exceptional-branch and low-a modular components remain to be formalized. Independent review and external novelty assessment are pending.

## November 3 original-source Lean inverse gateway

[ORIGINAL-INVERSE-BRIDGE-20261103.md](ORIGINAL-INVERSE-BRIDGE-20261103.md) documents an independently reconstructed, source-definition-importing proof from the authentic `SheepEven.EvenEdge` graph and blank even section 10 to two necessary inverse Diophantine branches. The kernel-checked dependency chain includes `SheepEvenInverseAlgebra.lean`, `SheepEvenSourceAlgebra.lean`, `SheepEvenReachInverse.lean`, `Sheep138HighH.lean`, `Sheep138Exceptional.lean`, and `Sheep138Gateway.lean`. It proves all k that a genuinely reachable target `2^(138+4860*k)`, if reached, has a **blank-reachable generic** last parent with odd-block exponent `h<3`. The exceptional odd-part-three branch is ruled out for every k and all natural candidate source valuations. This is an unconditional mathematical exclusion of one kind of last predecessor, with Lean axiom reports restricted to `[propext, Classical.choice, Quot.sound]` or subsets, no sorry. The full r=138 gate remains unclassified in one Lean theorem because low-a/high-a generic predecessor filtering and child closures have not been integrated.

The earlier `UniformH.lean` r138 node0 h-cutoff had an exponent-offset mismatch: the theorem was true but at `141+4860*k`, whereas root y=2^j requires `138+4860*k`. The theorem is now corrected, and an independent source-linked proof in `Sheep138HighH.lean` proves the exact root h<3 consequence. All changes remain intermediate, and the original Sheep machine and BB(6) are unresolved.

### Completed original-source root-to-two-children theorem (November 3)

The genuine blank-10 Sheep even-return reachability theorem `Sheep138RootTwoChildren.root_reaches_one_child` now **kernel-proves the complete first predecessor classification** for every `2^(138+4860*k)`, simultaneously for all `k : Nat`. A reachable root power would have a preceding **genuinely blank-reachable** state `x` satisfying exactly one of:
`15*x+2=2^(141+4860*k)` or `81*x+68=2^(143+4860*k)`. This proof exhausts all special and generic cases, not only a finite inverse depth. It is source-linked to the original `SheepEven.EvenReach` and compiled locally under Lean 4.36.0-rc2 with only standard axioms.

Source dependencies: `SheepOddGap.lean` (universal signed gap), `Sheep138GenericHigh.lean` (root all-high-a elimination), and four SHA256-pinned Lean modules losslessly archived in [root138-lean.tar.xz.b64](root138-lean.tar.xz.b64). Run [reconstruct_root138.py](reconstruct_root138.py) to hash-check and restore the four modules. The exact detailed theorem, hashes and limitations are in [ORIGINAL-INVERSE-BRIDGE-20261103.md](ORIGINAL-INVERSE-BRIDGE-20261103.md). Two rational child families remain unclosed: this theorem is an all-k reduction of the holdout's possible halting gates, **not** a Sheep nonhalting proof or a BB(6) solution.

The two child branches' generic-last-parent gateways have also compiled in `Sheep138ChildGateway.lean`; they require the remaining source-level generic-parent modular closure. The full root result and child exceptional exclusions are intermediate because their novelty relative to existing external work and the complete Sheep proof are not established.

### November 3: original-blank-rooted all-k r138 exclusion completed in Lean

**Final checked theorem:** `Sheep138FullClass.root138_unreachable (k : Nat) : ¬ SheepEven.EvenReach 10 (2^(138+4860*k))`. The full chain compiled in local Lean 4.36.0-rc2 against the SHA-verified Agent16 original Sheep step/edge/reach modules. The kernel reports axioms `[propext, Classical.choice, Quot.sound]` for the final theorem, with **no sorryAx**. The authentic two-child reduction has been closed: child generic-high excludes arbitrarily large valuations; 62 child low-a residue certificates individually establish all-k exclusions using 221 representative period cases. All source-level actual reachability witnesses are preserved until contradiction.

**Reproduce:** [reconstruct_root138.py](reconstruct_root138.py) restores four root Lean modules from hash-checked archive; [reconstruct_child138_high.py](reconstruct_child138_high.py) restores two high-a child Lean modules from a second hash-checked archive; [generate_full138.py](generate_full138.py) generates and SHA256 verifies the 62-child-residue, 62-source-case, and final-universal-exclusion Lean modules. The existing manual [source CI](../../.github/workflows/agent22-sheep-source-bridge.yml) includes the complete build chain, but the last dispatch failed during runner startup, and a pinned-upstream CI success is pending. All reproducibility hashes, theorems and verification scope are in [ORIGINAL-INVERSE-BRIDGE-20261103.md](ORIGINAL-INVERSE-BRIDGE-20261103.md).

The all-k r138 family is now **proved unreachable in Lean under source-level Sheep even-section semantics**. Other Sheep halting-power exponent classes and the BB(6) universal upper bound remain open. This is an intermediate, potentially reusable formalized exclusion and is retained in `im-results/` pending independent review of exact source transport, external novelty, and CI toolchain reproduction.


## November 3 source-CI confirmation and four exact inverse-cone structures

**Source-CI evidence update:** [manual run 41697791436](https://github.com/FlareZ123/bb6/actions/runs/41697791436), job 126132808019, actually ran and successfully compiled the complete original-import `Sheep138FullClass.root138_unreachable` Lean theorem on pinned upstream Cryptids and Lean 4.35.0-rc4. The final axiom audit was `[propext, Classical.choice, Quot.sound]`. The run's **overall failure** arose afterward in a separate Agent16 `ExceptionalEight.lean` file at lines 51 and 65, so it is incorrect to cite the *workflow* as having succeeded. Full exact provenance: [ORIGINAL-INVERSE-BRIDGE-20261103.md](ORIGINAL-INVERSE-BRIDGE-20261103.md).

A new synthesis [ROOT-FREE-CONES.md](ROOT-FREE-CONES.md) proves at the paper-plus-exact-arithmetic level that **all four** already-known infinite E-excluded powers `r+4860*k`, `r∈{138,402,1218,1738}`, have **exactly three** ancestors in their full even-section inverse reachability set, including the target. The r138/r1218 cases fork to two indegree-zero immediate parents; r402/r1738 have two-edge chains. Reproducible [exact_cones.py](exact_cones.py) checks every symbolic node with a full-period modular certificate and independently tests the literal exact E inverse for two representative exponents; [prior_overlap.py](prior_overlap.py) independently compares to the published 3,596/5,400 F-depth-five sieve and its SHA256. All four E families are disjoint from that older sieve, though their exclusion was recorded earlier by Agent14, and only r138's **blank exclusion** has currently passed pinned original-source Lean. No full-family source Lean certificate or Sheep machine decision has been asserted.
