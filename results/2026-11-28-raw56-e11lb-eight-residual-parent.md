# Source-accepted Raw56 E1=1LB eight-residual parent classification

**28 November 2026.** Lean 4.36.0-rc2, original six-state/two-symbol Turing-machine semantics.

Let the partial six-state table be
```
1RB---_1RC---_0RD---_1LD1LE_---1LB_------
```
with six unspecified transitions. **Theorem** (`BB6.Agent4Raw56LB.E11LB.reduced_quotient`): for any full machine `m` with `TNFQuotientCompatible p m`, either `WeightedBound 1000000 m`, or `TNFQuotientCompatible q m` for some `q` in the exact list `[table21049, table23706, table39232, table39234, table39233, table42763]`.

The original-source proof was **accepted by Lean** in [GitHub Actions 46148226109](https://github.com/FlareZ123/bb6/actions/runs/46148226109), artifact **15264856912**, with transitive axioms exactly `[propext, Classical.choice, Quot.sound]`. It has no `sorryAx`, external oracle, or simulation-cutoff assumption.

## Finite audit and proof technique

The exhaustive 43,348-leaf partial audit has 24 top-child branches and 26 individually checked certificate/cut/long submodules. Its exact parent Boolean checker theorem `ctop : canonicalCheck 1000000 ptop 5 ttop = true` passed [CI 46144287707](https://github.com/FlareZ123/bb6/actions/runs/46144287707), artifact **15264155789**.

Earlier attempts to kernel-check the entire parent *residual trace list equality* ran beyond reliable CI compiler time. Instead, [`CanonicalResidualSubset.lean`](../im-results/agent4-raw56-root-pilot/CanonicalResidualSubset.lean) proves a generic compositional lemma: if every child residual machine is among an allowed finite set, then so is every parent residual machine. This lemma passed [CI 46145859654](https://github.com/FlareZ123/bb6/actions/runs/46145859654), axioms `[propext, Quot.sound]`. All **24 child membership proofs**, the exact literal table equalities and the resulting **root membership theorem** `root_residual_subset` passed [CI 46147989191](https://github.com/FlareZ123/bb6/actions/runs/46147989191), artifact **15264696923**. The final `reduced_quotient` uses this subset classification with the source-accepted parent checker and already-proved bounds for the first two residual tables.

The eight residual identifiers are **M6168, M21109** (two bounded long-machine leaves), and **M21049, M23706, M39232, M39234, M39233, M42763** (six independently source-accepted universally nonhalting one-hole families). The last independent proof, [M23706](2026-11-28-raw56-m23706-quotient-nonhalting-agent4.md), passed [CI 46135562496](https://github.com/FlareZ123/bb6/actions/runs/46135562496). The auditable generator is [`gen_lb_subset_parent.py`](../im-results/agent4-raw56-root-pilot/gen_lb_subset_parent.py). The sixth successor case correctly uses a canonical cutoff of **6**, namely `max 5 (next.val+1)`.

## Formal scope

This closes the **exhaustive parent classification** of one Raw56 six-hole sibling, not BB(6) globally. The original-source **conditional six-machine Cover consumer** independently passed [CI 46145468843](https://github.com/FlareZ123/bb6/actions/runs/46145468843). A final unconditional physical-machine `Cover (WeightedBound 1000000) p` integration is being checked separately. Its acceptance should be reported only after that final source proof passes. The other Raw56 and global maximality obligations remain open.
