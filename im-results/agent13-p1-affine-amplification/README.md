# Finite P1 inverse-shadow graphs amplify to infinite affine families

**Agent 13, 2026-11-05. An abstract all-parameter theorem, proved in Lean 4.36.0-rc2.** This work addresses reusable proof technology for the P1 holdout. It does **not** alone decide the original Turing machine or BB(6); the original-source P1 bridge remains a separate obligation for any application to a critical halting target.

## A finite-to-infinite theorem

Define the exact shadow recurrence at an integer parameter q and side offset s by

```text
(m,z) -> (m+t+1,z') when
    z = 2^t v
    2 z' + 1 = 16 q + s + m + t + v .
```

It has increasing nonnegative cost coordinate m and positive residual coordinate z. Consider a chosen start (m0,z0). Assume its **entire** base-q orbit, with all legal choices of t at each step, is bounded by

```text
m ≤ M,       0 < z < 2^K .
```

Set `D=M+K+1` and `Δ=2^D`. For any start slope `S0` divisible by Δ and **every** r≥0, the complete recurrence from (m0,z0+S0·r) at the shifted parameter q+Δ·r also satisfies m≤M. More strongly, for every lifted reachable (m,z), there are a base-q reachable coordinate `zb` and a slope `S` satisfying

```text
z = zb + S·r,           2^(D-m) divides S.
```

**Lean theorem:** `BB6.Agent13Affine.finite_base_amplifies` in [FiniteToCylinder.lean](FiniteToCylinder.lean). Its local Lean4.36.0-rc2 `#print axioms` is exactly `[propext, Quot.sound]`. The assumptions quantify over **all reachable base states**, rather than finite-time samples or just one selected path.

## Proof of stability and exactness

Induct on the actual lifted inverse path. At a state with base coordinate zb and slope S divisible by `2^(D-m)`, the base bound m≤M implies `2^(K+1)` divides S. Since `0<zb<2^K`, the lifted coordinate `zb+S·r` has the same nonzero remainder modulo `2^K` as zb. Thus no inverse depth t≥K is legal. For every possible t<K, both coordinates have the same divisibility by `2^t`. If a lifted input is `2^t·v`, it can be written uniquely as

```text
zb = 2^t·v0,     S = 2^(t+1)·a,     v = v0 + 2 a r.
```

The next lifted recurrence then becomes

```text
2z' + 1 = (16q+s+m+t+v0) + 2(8Δ+a)r.
```

It follows that the base transition at the identical t exists, with next coordinate zb', and that `z'=zb'+(8Δ+a)r`. The child cost is `m'=m+t+1≤M` by the base bound. The slope divisibility invariant persists because `S=2^(D-m)·factor`, hence `a=2^(D-m')·factor`, and Δ is divisible by `2^(D-m')`. The induction therefore closes all lifted branches and cannot acquire a new edge. All statements are over exact natural-number arithmetic; no asymptotic approximation is used.

[AffineStability.lean](AffineStability.lean) proves the critical step decomposition and modular-depth stability without an axiom or `sorry`. [AffineGraphTheorem.lean](AffineGraphTheorem.lean) separately proves a finite-list certificate soundness result: any verified list of affine nodes with base-q closure and slope equations contains every lifted shadow state for every r. The finite-to-infinite theorem uses a base-reachability bound directly, so an explicit affine list at every r is unnecessary.

## Computational corroboration and structural significance

A separate exact-integer Python prototype unfolded *all* base inverse paths and computed the formula `S'=8Δ+S/2^(t+1)`. It compared lifted graphs with independently enumerated graphs at r=0,1,2,7 for q=29,30,31,33,61,94,158 and both P1 feeder sides. Every comparison agreed. Base graph sizes ranged from two nodes to 118, with inverse-cost maxima up to 41. These experiments validate the implementation and are secondary to the quantified Lean theorem.

The result explains mathematically why Agent8's successful q29+1024r 26-node cylinder and Agent13's source-certified q30+256r 22-node cylinder are possible. Their concrete moduli are much smaller than the theorem's conservative sufficient `2^(M+K+1)`. The generic theorem provides an automatic, finite-to-infinite amplification principle for any shadow seed with a fully proved finite base bound. It can avoid creating a new large symbolic affine graph by hand.

## Application boundary and next steps

The theorem is about the **shadow recurrence**, structurally identical to that in the source-proved Agent9 `ShadowFiniteInvariant.lean`. Its Lean code currently defines the recurrence independently and has not imported the original P1 `OddCone` or Turing-machine semantics. To turn a new base graph into an original-source critical exclusion, prove that authentic inverse cones enter the shadow recurrence, preserve the needed no-256/divisibility and mass constraints, and close even-right and c=1 exits using source lemmas. The previously certified Agent8/13 source-specific results already do these extra steps for their own residue classes. A generic original-source adapter would multiply the usefulness of this theorem.

No unverified generalization from `m≤M` to nonhalting of P1 is claimed. No global upper bound on BB(6) follows, and external mathematical prior-art novelty has not been audited.

## Verification

Run the **manual-only** source-independent [Lean workflow](../../.github/workflows/agent13-affine-amplification.yml) for the three source modules; all are written for pinned Lean4.36.0-rc2. The locally compiled theorems have only `[propext, Quot.sound]` axioms. The workflow result will be recorded here after execution.


## Completed genuine-source audits and a concrete instance

**Every required verification has now succeeded:**

- Pure abstract original Lean proof [run 42079277606](https://github.com/FlareZ123/bb6/actions/runs/42079277606).
- Unchanged original Agent9 `ShadowReach` adapter, [run 42079809856](https://github.com/FlareZ123/bb6/actions/runs/42079809856).
- Generic finite-list-to-infinite original-source theorem [run 42080832341](https://github.com/FlareZ123/bb6/actions/runs/42080832341).
- Concrete q30 original-source L0 and L1 examples [run 42081117977](https://github.com/FlareZ123/bb6/actions/runs/42081117977).

The [AffineSourceAdapter.lean](AffineSourceAdapter.lean) module proves an exact *two-way* translation between the abstract recurrence and the **unchanged original** `BB6.Shadow.ShadowReach` relation. Its `source_shadow_finite_lift` theorem gives the same universal infinite-parameter conclusion in Agent9's original source notation. [AffineSourceList.lean](AffineSourceList.lean) removes the quantified base-orbit assumption: given a finite list containing the root, with every listed state within bounds and each exact source shadow edge closed under the list, `finite_list_source_amplifies` proves the entire infinite progression. All are kernel-verified with only standard axioms.

[P130AmplifiedShadow.lean](P130AmplifiedShadow.lean) instantiates this **generic** result using the already certified 13+9 base nodes of the q30 P1 example. For every r≥0, all original Agent9 shadow states of each feeder rooted at q=30+2^20·r have inverse cost m≤10. This instance uses a conservative generic modulus 2^20; the earlier hand-specialized Agent13 P1 result already proves a much denser q=30+256r family and full genuine blank-root critical-target nonreachability. The generic instance is a **reusable-method demonstration**, not an additional independent P1 critical-target family.

The finite-list certificate is a purely checkable set of integer equations; future research can replace the example list with finite base-q graph certificates generated by an exact enumerator. Additional original odd-cone, even-exit, exceptional-input, and reset-gateway obligations remain necessary to turn an amplified shadow bound for another q into an actual P1 halting-decision result. The new generic theorem itself has no assumptions about unproven Turing-machine behavior.
