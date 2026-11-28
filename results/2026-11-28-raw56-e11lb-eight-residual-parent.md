# Complete original-source Raw56 E1=1LB six-hole Cover

**28 November 2026.** Lean 4.36.0-rc2, original six-state/two-symbol Turing-machine semantics.

Let the partial six-state table be
```
1RB---_1RC---_0RD---_1LD1LE_---1LB_------
```
with six unspecified transitions. **Theorem** (`BB6.Agent4Raw56LB.E11LB.reduced_quotient`): for any full machine `m` with `TNFQuotientCompatible p m`, either `WeightedBound 1000000 m`, or `TNFQuotientCompatible q m` for some `q` in the exact list `[table21049, table23706, table39232, table39234, table39233, table42763]`.

**Complete local theorem:** `BB6.Agent4Raw56LB.E11LB.all : Cover (WeightedBound 1000000) p`, together with `all_quotient` for every quotient-compatible completion, has now passed the original-source Lean 4.36.0-rc2 acceptance gate [run 46148466766, job 140989576666](https://github.com/FlareZ123/bb6/actions/runs/46148466766/job/140989576666), artifact [15264389640](https://github.com/FlareZ123/bb6/actions/runs/46148466766/artifacts/15264389640), ZIP SHA-256 `73576266f217e1970e33f5b00be9847fa8ba2a88c55a2d7bed7bd6415ae400f9`. Both final theorem profiles contain exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx` or external oracle. The 1LB six-hole parent is therefore completely covered at weighted bound 1,000,000, across all **25^6 = 244,140,625** physical compatible completions.

**Parent classification step:** The original-source proof was **accepted by Lean** in [GitHub Actions 46148226109](https://github.com/FlareZ123/bb6/actions/runs/46148226109), artifact **15264856912**, with transitive axioms exactly `[propext, Classical.choice, Quot.sound]`. It has no `sorryAx`, external oracle, or simulation-cutoff assumption.

## Finite audit and proof technique

The exhaustive 43,348-leaf partial audit has 24 top-child branches and 26 individually checked certificate/cut/long submodules. Its exact parent Boolean checker theorem `ctop : canonicalCheck 1000000 ptop 5 ttop = true` passed [CI 46144287707](https://github.com/FlareZ123/bb6/actions/runs/46144287707), artifact **15264155789**.

Earlier attempts to kernel-check the entire parent *residual trace list equality* ran beyond reliable CI compiler time. Instead, [`CanonicalResidualSubset.lean`](../im-results/agent4-raw56-root-pilot/CanonicalResidualSubset.lean) proves a generic compositional lemma: if every child residual machine is among an allowed finite set, then so is every parent residual machine. This lemma passed [CI 46145859654](https://github.com/FlareZ123/bb6/actions/runs/46145859654), axioms `[propext, Quot.sound]`. All **24 child membership proofs**, the exact literal table equalities and the resulting **root membership theorem** `root_residual_subset` passed [CI 46147989191](https://github.com/FlareZ123/bb6/actions/runs/46147989191), artifact **15264696923**. The final `reduced_quotient` uses this subset classification with the source-accepted parent checker and already-proved bounds for the first two residual tables.

The eight residual identifiers are **M6168, M21109** (two bounded long-machine leaves), and **M21049, M23706, M39232, M39234, M39233, M42763** (six independently source-accepted universally nonhalting one-hole families). The last independent proof, [M23706](2026-11-28-raw56-m23706-quotient-nonhalting-agent4.md), passed [CI 46135562496](https://github.com/FlareZ123/bb6/actions/runs/46135562496). The auditable generator is [`gen_lb_subset_parent.py`](../im-results/agent4-raw56-root-pilot/gen_lb_subset_parent.py). The sixth successor case correctly uses a canonical cutoff of **6**, namely `max 5 (next.val+1)`.

## Formal scope

This establishes an **unconditional original-source Cover of the entire Raw56 E1=1LB six-hole sibling**, not BB(6) globally. The separately accepted six-machine conditional consumer [CI 46145468843](https://github.com/FlareZ123/bb6/actions/runs/46145468843) is now composed with the authenticated parent reduction by the final accepted `Raw56LBCompleteHybrid` build. The acceptance workflow replaces its historical import `Raw56LBE11LBReduced` with the accepted `Raw56LBTopSubsetReduction`; its immutable artifact contains the exact compiled source. The staged `Raw56Root13LB.lean` local root-14-to-13 consumer **has not yet been source-accepted**. Neither the complete Raw56 parent nor the global 38-case BB(6) upper bound follows from this sibling Cover. Reproduction: invoke the existing manual `.github/workflows/agent4-raw56-lb.yml` target `complete-subset` at source revision `8a31526d8d8c2900ef06098c9a51c41f2d8abd36`, using parent run 46148226109, M23706 run 46135562496 and M39232 run 46135066154.
