# Exact source-integration program for the Sheep 648 two-node inverse cone

Agent14, 2026-11-05. **Scope: active intermediate research.** The mathematical arithmetic cone has a verified proof certificate and several no-sorry Lean components. The complete original-source all-k `EvenReach` theorem is not yet assembled. The objective here is a *single genuine blank-reachability theorem* that consumes the existing components.

## Two nodes and original-source graph

Set `j=648+122472*k`. Let `R=2^j` and `X=(2^(j+8)-1228)/2187`, both integer for every k. Original-source first-even graph `SheepEven.EvenEdge` is the source-connected target relation, with original even root 10.

The complete verified arithmetic E inverse DAG has exactly one incoming E edge to R, from X. No even source has an E edge into X. A source-last-edge theorem and the finite inverse-DAG induction already exist:

- [SheepEvenSourceAlgebra.lean](../agent14-sheep-even-inverse/SheepEvenSourceAlgebra.lean) contains `original_even_edge_inverse_cases` for a target `d*y+c=2^n`, covering generic and exceptional sources.
- [SheepEvenReachInverse.lean](../agent14-sheep-even-inverse/SheepEvenReachInverse.lean) contains a source-valid reachability last-edge splitter.
- [SheepSourceFiniteInverseDAG.lean](SheepSourceFiniteInverseDAG.lean) proves `no_blank_reach_of_finite_inverse_DAG` on genuine `EvenReach 10` with a finite strict index, verified with the original Cryptids machine source in [CI 42083000740](https://github.com/FlareZ123/bb6/actions/runs/42083000740).

To instantiate the two-node DAG for each k, define `node : Fin 2 → Nat` with `node 0=R` and `node 1=X`. Show neither is 10, every incoming even edge to R has source X, and no even incoming edge to X. Applying the certified DAG theorem yields `¬ EvenReach 10 R`, for every k.

## Exhaustive original-source predecessor table

For each original-source generic E last edge to a node y with `d*y+c=2^n`, its exact existing source theorem gives natural `a≥1`, `v` odd ≥5, `h`, `u` odd, and:

```
(d*3^h)*(2^(a+1)+1)*v + 2*a*(d*3^h)
 + 2^(h+1)*(d+c)
 = 2^(n+h+1)+3*(d*3^h).
```

For exceptional odd part three it gives:

```
(d*3^h)*(3*2^a+a+2) + 2^h*(d+c) = 2^(n+h).
```

There are two exact target tuples `(d,c,n)`:

- Root `(1,0,648+122472k)`. [Sheep648HighH.lean](Sheep648HighH.lean) kernel proves `h<6`, based on the root's nontrivial residue modulo 729 for every k.
- Child `(2187,1228,656+122472k)`. The same module kernel proves `h=0`, based on the exact residue modulo 6561.

For these seven `(node,h)` rows, the finite low-a bounds are computed by the standard `K(a)` linear-versus-exponential induction. Every `a≥A` is mathematically impossible by [SheepSevenGenericHigh.lean](SheepSevenGenericHigh.lean) combined with [SheepOddGap.lean](../agent14-sheep-even-inverse/SheepOddGap.lean)'s universal signed odd small-remainder theorem. The first module is already checked for each of the seven rows [CI 42082468905](https://github.com/FlareZ123/bb6/actions/runs/42082468905). **Missing original-source step:** turn each row's precise generic inverse equality into the signed-modulus premise. [Sheep648RootHigh0.lean](Sheep648RootHigh0.lean) is a first standalone test of this source-shaped bridge for the root h=0 case, with CI at [.github/workflows/agent14-sheep-648-high0-lean.yml](../../.github/workflows/agent14-sheep-648-high0-lean.yml). Its status must be checked independently before citing success.

For `1≤a<A`, a total of 57 possibilities exist. Precisely the root `h=5,a=2` is allowed. All **56 excluded** `(node,h,a)` instances have standalone proven all-k modular nonmatches [CI 42084801886](https://github.com/FlareZ123/bb6/actions/runs/42084801886). More strongly, every forbidden original-source *generic integer equation above*, specialized to these same 56 fixed pairs and arbitrary k and v, is contradicted by the appropriate modular theorem in 56 isolated generated Lean files:
[generate_648_source_low.py](generate_648_source_low.py), [CI 42087899261 success](https://github.com/FlareZ123/bb6/actions/runs/42087899261).
These separate files must be compiled into `.olean` modules and imported or otherwise assembled by a source-general finite case decision theorem; simple `lean` processing of them as individual inputs does not automatically make them importable into later modules.

For all seven special source h cases, [SheepSevenSpecial.lean](SheepSevenSpecial.lean) proves that no natural a can satisfy the corresponding exceptional equation, uniformly in k [CI 42082468905](https://github.com/FlareZ123/bb6/actions/runs/42082468905). The **missing original-source step** here is a small algebraic normalization showing the special equation from `original_even_edge_inverse_cases` has the same coefficients as the already-proved `special_648_i_h`.

## The unique admissible parent identity

If `y=2^j=1+3^5*u` and the generic even-section source has `a=2`, its exact return equation is

```
2*(1+2^5*u)+1=(2^3+1)*v+2*2,
x=2^2*v.
```

Rearranging gives `9v=64u-1`, `243u=2^j-1`, and

```
2187*x+1228 = 2^(j+8).
```

Thus the only genuine even parent of the root belongs to the child node and, if reached from 10 before the root, is likewise genuinely blank-reachable. A *source theorem* establishing this algebra and the child no-incoming theorem completes the two-node DAG. Actual original-blank semantics and final `¬EvenReach 10` then follow from the already authenticated source modules.

## Research-priority and claim boundary

The new nonreachability claim is justified as a **paper proof with complete arithmetic certificates**. The precise source-level machine connection has now been tested for the finite low-a branches and true 3-adic hidden bounds in no-sorry Lean, and its general DAG-consumption theorem is authentically checked. **No full new root exclusion in unchanged-source Lean has yet been claimed.**

This work remains a local infinite forbidden exponent family in one holdout, with no BB(6) upper bound or Sheep machine decision. Its strongest potential improvement is the reusable source-root finite-cone proof method, which could apply to other hard machines. For global BB(6) progress, source-sensitive invariants or complete unresolved-root arguments are still needed.
