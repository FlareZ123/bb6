# Machine C: rigidity of linear ranks at primitive and section scales

**Status:** kernel-checked structural theorems, not a decision of Machine C or BB(6). Results stay in `im-results/` because no new six-state machine classification or busy-beaver bound follows.

The maps are the repository's existing **original** Machine C counter maps, not synthetic approximations:

- Primitive three-counter `BB6CLine.nextC` from [CLine.lean](../agent11-c-line/CLine.lean).
- Complete two-counter return `BB6.Agent46.secNext` from [FastSectionDef.lean](../agent46-c-jump/FastSectionDef.lean).

Their previously known monotonic ranks were `a+2*k+c` (primitive) and `a+2*k` (complete sections). The new theorem is **necessity and uniqueness**: no other nonnegative integral linear weight vector is monotone on every successful source transition.

## Exact three-counter theorem

For arbitrary `u,v,w:Nat`, write `P(a,k,c)=u*a+v*k+w*c`. Theorems `machine_c_primitive_linear_unique` and `machine_c_primitive_no_strict_linear` in [PrimitiveRankOriginal.lean](PrimitiveRankOriginal.lean) prove:

```text
(∀ s t, nextC s = some t → P(s) ≤ P(t))  ↔  w = u ∧ v = 2*u

¬ (∀ s t, nextC s = some t → P(s) < P(t))
```

Three genuine source families force the three necessary inequalities:

1. Sweep `(1,0,4) → (0,1,3)`: `v ≥ u+w`.
2. Zero-left reset `(0,k,0) → (1,0,2k+2)` for all `k`: `v ≤ 2w`.
3. Even bounce `(0,2j,4) → (4j+2,2,1)` for all `j`: `v ≤ 2u`.

Together they imply `u=w` and `v=2u`. Sufficiency is the existing exact-source `BB6CLine.rank_mono` theorem. The sweep family preserves `P` at equality for every such triple, so **a globally strictly increasing linear primitive rank does not exist**, including for nonzero coefficients. This explains the necessity of a secondary component in Agent 42's previously proved lexicographic `(a+2k+c, a+c)` rank.

The general source-independent proof is [PrimitiveRankUnique.lean](PrimitiveRankUnique.lean), avoiding asymptotic assumptions by choosing finite witness indices as explicit functions of the candidate weights.

## Exact two-counter section theorem

For arbitrary `u,v:Nat` and `L(a,k)=u*a+v*k`, [MachineCLinearRankOriginal.lean](MachineCLinearRankOriginal.lean) establishes

```text
(∀ s t, secNext s = some t → L(s) ≤ L(t)) ↔ v = 2*u

(∀ s t, secNext s = some t → L(s) < L(t)) ↔ 0 < u ∧ v = 2*u
```

The direct family `(2k,k) → (0,2k+2)` forces `v≥2u`; the short even-bounce family `(2k+1,k+1) → (4k+2,3)` forces `v≤2u`. Both are proved from the unchanged `exactSection`/`bounce` definitions for all `k≥1`. The sufficiency direction reuses Agent 3's already established `section_rank_strict`. The general kernel theorem is [MachineCLinearRankRigidity.lean](MachineCLinearRankRigidity.lean).

## Verification and relevance

- Source-closure CI for the two-counter theorem **passed**, [run 45258467939](https://github.com/FlareZ123/bb6/actions/runs/45258467939), Lean 4.36.0-rc2. Both concluding source theorems report only `[propext, Classical.choice, Quot.sound]` in their Lean axiom dependencies.
- The primitive three-counter proof **passed full unmodified-source Lean CI**, [run 45259644484](https://github.com/FlareZ123/bb6/actions/runs/45259644484), in the existing manual `agent3-u5-m32-w485-highstop.yml` workflow with target `linear-rank`. The two concluding original-source theorems have axiom profile **`[propext, Quot.sound]`**, without `sorryAx`, `native_decide`, or `Classical.choice`. The same run recompiled the two-counter theorem successfully.

**Impact:** the theorem rules out improving the global section-rank obstruction or replacing the primitive lexicographic ranking using a different nonnegative linear functional. It does not prove nonhalting, halting, a new density bound, or a new bound on BB(6); resolving those questions requires nonlinear invariants or root-specific ancestry arguments.
