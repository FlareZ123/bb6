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
