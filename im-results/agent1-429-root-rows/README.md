# BB429 source-root row restrictions and two complete modulus-65536 terminal exclusions

**Intermediate research, Agent 1, 2026-11-05.** The Lean 4.36.0-rc2 original-repository source audit **passed** [GitHub Actions 42109142691](https://github.com/FlareZ123/bb6/actions/runs/42109142691). All resulting `#print axioms` output contains only standard Lean axioms, with no `sorryAx`. This dossier addresses the true blank-root accelerated machine #429. It does **not** decide the original six-state machine or BB(6), and no outside-literature novelty audit has been completed.

## Rooted invariants

[BB429NewRootRows.lean](BB429NewRootRows.lean) imports the authentic `BB429.next` from Agent 5 and the prior true-root positive-even condition from Agent 39, `BB429RootEven8.rooted_positive_even_eight`:

* For every `n,a,b`, if `BB429.run n (0,0) = some (a,b)` and `a%16=11`, then `b%8 ∈ {2,6,7}`.
* For every `n,a,b`, if that same run reaches `(a,b)` and `a%32 ∈ {19,27}`, then `b%8 ∈ {2,7}`.

Both restrictions are quantified over all time and counter values. Each underlying one-step result is established by exhaustive unfolding of the source successor cases and `omega`, with no bounded search.

## Two entire parameter-uniform terminal families

[BB429InverseKernelExtended.lean](BB429InverseKernelExtended.lean) copies Agent 33's all-parameter affine `cert` and soundness proof, extending the existing six independent root-disjoint leaf tests with the two new conditions. It explicitly analyzes every legal necessary inverse branch (F/S/E) at depths up to 14.

[BB429NewRootGate16.lean](BB429NewRootGate16.lean) has a terminating, kernel-checked `by decide` certificate for **every** parameter `q : Nat`, proving:

```lean
BB429NewRootGate16.blank_halt_not_11473 :
  ∀ n a b, BB429.run n (0,0) = some (a,b) →
    b+1=2*a → a%65536≠11473

BB429NewRootGate16.blank_halt_not_57341 :
  ∀ n a b, BB429.run n (0,0) = some (a,b) →
    b+1=2*a → a%65536≠57341
```

The residue projections modulo 8192 are **3281 and 8189**, respectively. Neither occurs among Agent 33's original 38 excluded whole cylinders modulo 8192, so this is a genuine strengthening of that explicit baseline. It is independent of any particular finite run length. Earlier source-proven gates and other agents' stronger modular results remain relevant; no claim of absolute priority among all internal/external results is made.

## Reproduction and limits

The manual-only [source-check workflow](../../.github/workflows/agent1-429-root-rows.yml) imports the actual repository `BB429Rank`, `BB429Mod8`, `BB429RootEven8`, `BB429NewResidue`, `BB429RootMod16`, `BB429RootMod32`, then both new root and inverse modules, verifying proofs and printed axioms. [Run 42109142691](https://github.com/FlareZ123/bb6/actions/runs/42109142691) passed; the preceding failed run exposed only an `end` namespace typo that was corrected in the successful run.

The existing upstream-source bridge `BB429SourceMod16.source_run_to_local` identifies genuine original Cryptids sections with the same local run, and `source_next_none_to_local` identifies genuine terminal branches. An explicit final theorem in the pinned unchanged Google DeepMind Cryptids source is a separate integration task unless independently audited.

The certificate does not claim any surviving terminal cylinder is actually reachable. Arbitrarily deep inverse-feasible synthetic paths exist, and these two exclusions alone leave infinitely many possible true-root terminals. The productive next step is to find a nonperiodic, history-sensitive, all-parameter obstruction covering an entire remaining root-halting component, or a genuine source halting witness, rather than simply counting higher-modulus leaf filters.
