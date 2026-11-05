# Parametric 26-node P1 shadow graph for q = 29 + 1024r

**Agent 8, 2026-11-05. Intermediate inverse-cone mathematics.** This investigation extends Agent 9's already source-verified *fixed* q=29 two-feeder shadow certificate to an infinite arithmetic progression. It is not a BB(6) value, P1 nonhalting theorem, or original critical-target exclusion.

## The exact candidate theorem

Set `q=29+1024r`, `N=16q`, `u+4q+3=7*2^N`, with `u≥1`. On Agent 45's two authentic P1 feeder roots

- L0: `(b0,d0)=(4u-4,4u+9)`, `L=N+8`, starting shadow `(m,z)=(0,12q+4)`;
- L1: `(b0,d0)=(6u-2,2u+5)`, `L=N+9`, starting shadow `(m,z)=(0,10q+4)`,

each authentic finite source `OddCone b0 d0 b d m` with `b%4=0` has `m≤10`. This bounds the cumulative odd inverse cost independently of `r`, even though the original counters grow exponentially.

The certificate is the complete affine set of twelve L0 nodes and fourteen L1 nodes in [CylinderArithmetic.lean](CylinderArithmetic.lean). Each node has form `(m,z0+s*r)`. The source shadow recurrence is

```text
z = 2^t*v
2*z' + 1 = L + m + t + v
(m,z) -> (m+t+1,z')
```

The kernel proof verifies at every `r≥0` that these explicit lists contain the initial nodes, every shadow edge remains in the appropriate list, `m≤10`, `z>0`, and `256∤z`. From `256∤z`, any exact edge has `t≤7`, so all infinitely many possible inverse histories reduce to finite affine arithmetic. Importantly, the finite node count is uniform while each node's right coordinate is unbounded as `r` grows.

## Verification and precise provenance

- [CylinderArithmetic.lean](CylinderArithmetic.lean) was compiled *locally* with Lean 4.36.0-rc2. Both `l0_closed` and `l1_closed` report exactly `[propext, Quot.sound]`; no admitted statements or source assumptions.
- [CylinderSource.lean](CylinderSource.lean) composes the arithmetic proof with Agent 9's authentic `finite_shadow_invariant_lifts_full_cone` and `two_feeder_root_arithmetic` statements. It type-checked locally against matching interface signatures. **The local mock interface has axioms, so its compilation is not original-source verification.**
- [Manual-only GitHub Actions](../../.github/workflows/agent8-p1-shadow-cylinder.yml), dispatched as [run 42065792288](https://github.com/FlareZ123/bb6/actions/runs/42065792288), builds the unchanged original Agent 1/47/9 source definitions before the new arithmetic/source modules and checks for `sorryAx`. **This source audit was queued at the initial README checkpoint.** A finished successful run with standard-only axioms is required before upgrading the result's provenance.
- Independent finite exact-integer tests checked `r=0,1,2,3,7,99,1000`, obtaining 12 L0 and 14 L1 nodes, maximal `m=10`. Finite checks are exploratory, supplementary to the quantified Lean arithmetic theorem.

## Prior work, overlap, and missing obligations

The recurrence, source authenticity bridge, q=29 seed, exact 26-node base graph, and full-cone inductive induction method are **Agent 9's existing work** in [their source dossier](../agent9-p1-shadow/README.md) and original CI [42043587196](https://github.com/FlareZ123/bb6/actions/runs/42043587196). The new observation is a *single 26-node affine invariant uniform for all* `r≥0`. This is mathematical strengthening of the quantified source inverse-cost statement, subject to source verification and later novelty review.

For P1, `n=16q+2=466+16384r`. Agent 12 already source-certified actual critical nonreachability for `n≡466(mod65536)` ([dossier](../../results/2026-11-02-p1-eight-new-n2mod16-families-agent12.md)). That known class is `r≡0(mod4)` within the present progression. **No new full critical nonreachability theorem is claimed for any other r.** The source odd inverse-cost bound alone does not rule out all actual even-output, exceptional `c=1`, smaller-left, or odd-source root ancestry cases.

The most valuable next theorem is a genuine-source complete exit exclusion using a uniform exact inverse-depth bound (the affine graph gives `t≤7`), the already source-verified Agent 1 `medium_root_even_not_reachable` theorem, and a source c=1 obstruction. Once all other genuine predecessor types and two-feeder ancestry are covered, attempt an all-r actual critical `¬Reach 2 H(466+16384r)` statement and compare all previously certified residue families. Neither P1 nonhalting nor BB(6) follows without the remaining infinite critical sectors and other six-state machines.

## Source-certified generic all-q criterion (2026-11-05)

[GenericCritical.lean](GenericCritical.lean) proves `BB6.Agent8Generic.critical_unreachable_of_shadow` for arbitrary q≥29 and *arbitrary lists of two shadow nodes* satisfying root membership, full dyadic-step closure, m≤10, and absence of z divisible by256. This checker is **unconditional over all possible authenticated odd inverse source ancestors**; `GenericBlocked.lean` handles all genuine exceptional and even terminal exits. Original-source Lean4.36 [run 42109123502](https://github.com/FlareZ123/bb6/actions/runs/42109123502) succeeded, with precisely standard axioms.

The generic criterion was applied to Agent45's thirteen period-256 families in a separate all-original-source [CI 42110442046](https://github.com/FlareZ123/bb6/actions/runs/42110442046), producing an academically substantive batch of thirteen infinite critical-index classes. See [result synthesis](../../results/2026-11-05-p1-thirteen-period256-source-lift.md). This remains a finite-shadow sufficient condition and gives no classification of P1 configurations which lack such a small invariant.
