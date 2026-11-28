# Complete weight-only threshold criterion for partial Turing-machine audit trees

**Theorem (original-source Lean accepted, 28 November 2026).** An already authenticated `PartialAudit` tree admits a *necessary and sufficient* uniform weighted-bound test using only its first-query step counts and possible incoming blank delays, **provided every explicitly retained unresolved residual is independently bounded at the candidate threshold**.

The result extends the accepted exact-query-weight treatment of *closed* `Audit` trees to the **partial** audit representation used in the hardest six-state Busy Beaver cylinders. Unlike naive rechecking of an audit at a lower threshold, the weight-only test does not replay potentially hundreds of thousands of exact tape steps, cycle certificates, automata checks, or previously imported nonhalting theorems.

## Precise kernel statement

The proof is in [`im-results/agent11-partial-weight/PartialWeightExact.lean`](../im-results/agent11-partial-weight/PartialWeightExact.lean), with these exports:

```lean
BB6.Agent11PartialWeightExact.quick_weight_necessary
BB6.Agent11PartialWeightExact.weight_audit_necessary
BB6.Agent11PartialWeightExact.partial_weights_necessary
BB6.Agent11PartialWeightExact.partial_weights_exact
```

For partial table `p`, partial audit `t`, original checked weighted threshold `A` and desired new threshold `B`, the main statement is

```lean
theorem partial_weights_exact (A B : Nat) (p : PartialMachine)
    (t : PartialAudit)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p)
    (old : partialCheck A p t = true)
    (hres : ∀ e ∈ partialResiduals p t,
      ∀ m, compatible e.2 m → WeightedBound B m) :
    (∀ m, compatible p m → WeightedBound B m) ↔
      partialWeights B p t = true
```

The residual parameter `hres` is **essential**: an unresolved residual cannot be declared bounded by passing the query checks elsewhere in the tree. Its entire point is to preserve the exact remaining mathematical obligations. The necessity direction `partial_weights_necessary` does **not** use `hres`: any valid universal B-bound implies that every reachable query's exact incoming-zero-delay surcharge fits within B.

### Proof mechanism

Induction over the authenticated partial tree handles three cases:

- `unresolved`: the independent residual hypothesis supplies the bound; the weight-only predicate is vacuously true, with no unsound inferred closure.
- `closed t`: the completeness of individual query weights in an accepted full `Audit` (the previously original-source accepted `ZipWeightTighten.queryWeight_complete`) implies the necessary `weightAudit B` predicate.
- `split n slot kids`: the original checked query ensures the slot is genuinely the first unknown encountered, so any universal bound must pay each attainable incoming delay. The induction transfers to all 24 nonhalting refinements using `refine_preserves_compat` and `allMoves_sound`.

For the reverse implication, the previously original-source accepted `Agent32AuditReweight.partial_reweight` transfers the old `partialCheck A` certificate to `partialCheck B` without revisiting the tape or automata. Then `Agent47PartialAudit.partialSound` gives either `WeightedBound B` directly or an explicit compatible residual; `hres` discharges the latter. No axiom of decidable halting is assumed.

## Verified original-source artifact

[`shared-lean-source-closure.yml` run **46146755553**](https://github.com/FlareZ123/bb6/actions/runs/46146755553) source-compiled **55 project Lean modules** at exact root `im-results/agent11-partial-weight/PartialWeightExact.lean`, including its transitive source imports, then audited the final theorem. The job passed:

```text
'BB6.Agent11PartialWeightExact.partial_weights_exact'
  depends on axioms: [propext, Classical.choice, Quot.sound]
[lean-closure] SUCCESS: compiled 55 project modules from 1 root(s)
PASS: 1 distinct .partial_weights_exact theorems, only standard Lean axioms
```

Evidence artifact [**15264756714**](https://github.com/FlareZ123/bb6/actions/runs/46146755553/artifacts/15264756714) (`standalone-lean-source-closure`), ZIP SHA-256 `10ac14561d254f868439f4142573e14ff1dc55e1fc87fdbfefabbe28f8f3ad4d`.

The checker reports only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or `native_decide`. No C++ simulator output is trusted as a proof.

## Application to the newly completed Raw112 cylinder

The independently source-accepted [Raw112 full six-hole Cover](2026-11-28-raw112-six-hole-complete-source-accepted-agent11.md) proves `WeightedBound 100000` across all **25^6 = 244,140,625** completions. Its `PartialAudit` has **25,004 split nodes**, **446,232 cycle nodes**, and exactly **two** originally unresolved cylinders, both now independently certified nonhalting. In that specific case `hres` holds at *every* natural threshold `B`.

The new generic iff therefore enables a sharper complete-parent bound by source-checking `partialWeights B parent tree = true` and failing it at `B-1`, without rebuilding the 24 branch proof shards. An independently source-pinned but untrusted candidate computation [CI 46147673209](https://github.com/FlareZ123/bb6/actions/runs/46147673209) suggests the sharp weighted threshold **91,503**, with a first-halt query at **91,502** ordinary steps and zero incoming delay. **That number is not asserted here as proved**: its full original-source Lean threshold test and attaining witness are separately pending.

This method is general: any future hard cylinder with accepted partial audit and individually proved residuals can use the same exact weight-only criterion. In isolation it does not decide BB(6), remove a canonical global roster member, or certify a new numeric threshold.
