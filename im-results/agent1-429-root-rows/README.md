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


## Two-step odd/odd inverse obstructions and branch-10 application (draft)

The feature-branch module [BB429RootOddRowsStrong.lean](BB429RootOddRowsStrong.lean) now has two candidate all-time root obstructions:

- `rooted_not_9_5`: `Reach(a,b) ∧ a≥33 ∧ a%16=9 ∧ b%8=5 → False`.
- `rooted_not_13_1`: `Reach(a,b) ∧ a≥33 ∧ a%32=13 ∧ b%8=1 → False`.
- `rooted_not_5_1`: `Reach(a,b) ∧ a≥61 ∧ a%32=5 ∧ b%8=1 → False`.

Row 9/5 and row 13/1 use two successive `odd_back` decompositions. For row 9/5, both second-predecessor cases force a positive-even predecessor whose second counter is 1 mod 4, contradicting `even_back`. For row 13/1, the second-predecessor case gives the same even-back contradiction, while the first-predecessor case reaches a state with first counter 1 mod 8 and second counter 3 mod 4, excluded by `BB429Mod8.Allowed`. Row 5/1 follows a third inverse step: one branch contradicts `even_back`; the other reaches a positive-even first counter with second counter 6 mod 8, contradicting `rooted_positive_even_eight`.

[BB429LastResetRow95.lean](BB429LastResetRow95.lean) composes these root obstructions with the exact branch-10 last-reset prestate equation. It excludes the following refined residue progressions:

- Eight pairs `(n mod 64,d mod 32)=(7,7),(15,19),(23,31),(31,11),(39,23),(47,3),(55,15),(63,27)`, which force `x mod 16=9` and `y mod 8=5`.
- Eight pairs `(n mod 128,d mod 32)=(19,1),(27,13),(35,25),(67,9),(75,21),(107,5),(115,17),(123,29)`, which force `x mod 32=13` and `y mod 8=1`.
- Eight pairs `(n mod 128,d mod 32)=(3,25),(35,9),(43,21),(75,5),(83,17),(91,29),(115,1),(123,13)`, which force `x mod 32=5` and `y mod 8=1`.

The lower bound `x≥33` follows uniformly from `9(3n+77)≤2^(n+2)(d+6)` for `n≥18,d≥3`. [SourceLastResetRow95.lean](../agent6-harmonic429/SourceLastResetRow95.lean) transports both families to the original Cryptids `sourceRun` semantics through `BB429SourceMod16.source_run_to_local`.

The same two root obstructions have been added as terminal bad states in `BB429KernelExtended.Bad`, so the existing affine inverse-tree certificate can use them at arbitrary recursion depth. This is a reusable strengthening of the certificate engine, not yet a new machine decision.

The new 24 refined lifts (eight each in rows 9/5, 13/1, and 5/1) are only the additions in this branch. The complementary eight lifts and 12 earlier whole-class exclusions remain on the separate draft PR #102 branch; those modules are not yet integrated here. Agent 1's full residue audit reports 16 complete long-burst parameter classes eliminated and 28 remaining classes / 112 of 176 refined lifts. This is a finite modular classification of necessary-condition rows, not a proportion of machines or a #429 decision.

**Verification status:** the root-row workflow's earlier run 43714798173 failed on an argument-strength mismatch at `BB429RootOddRowsStrong.lean:26`; Agent 1 corrected that argument, but no fresh successful source CI is recorded. The new `rooted_not_13_1` and `rooted_not_5_1` theorems, all last-reset consumers, and the modified inverse-kernel certificate have not been locally compiled or source-CI checked. The next discriminating test is a local Lean 4.36.0-rc2 compile of the changed dependency closure, followed by one pinned source-chain check and transitive `#print axioms` audit. Do not treat these draft integrations as source-certified.

The finite short-branch residue reductions remain as previously described in the last-reset communications; they do not establish a complete root-halt exclusion.


### Reproducible finite certificate audit (not a proof)

The BigInt transcription at [audit_cert14.mjs](../agent6-429-last-reset-row95/audit_cert14.mjs) evaluates the depth-14 affine inverse certificate with the three new root predicates over every odd n in 19..529 and all four d mod 64 lifts of the 44 d mod 16 candidates in the current terminal-residue table. It checks 2,816 affine families: 1,984 certify, 16 of the 44 (n mod 32,d mod 16) classes certify completely, 27 certify partially, and one class has no certificate exclusion in this finite range: (23,7). This is a JS transcription of the Lean recursion, not a Lean evaluation and not a uniform-in-n theorem. The untouched (23,7) class is the next concrete holdout for inverse-tree refinement.
