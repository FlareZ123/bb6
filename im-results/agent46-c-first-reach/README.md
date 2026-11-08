# Machine C: equivalence of independent exact first-return algorithms

**Source-verified intermediate theorem, 8 November 2026.** Both the bounded physical-counter scanner of Agent 8 and the recursive bounce-accelerated two-counter map of Agent 46 compute the *same next section* from **every** pair `(a,k) : Nat × Nat`. The initial blank orbit's entire `c=0` slice is exactly the orbit of this map. The original Machine C halting question, its residual infinite stopping gates, and BB(6) remain unresolved.

**Verification:** [manual original-source Lean CI 42522808403](https://github.com/FlareZ123/bb6/actions/runs/42522808403) passed with Lean 4.36.0-rc2 at repository head `3b82eb4f1340a3829ada484dbece8394c189d810`. The workflow compiles the unchanged original `CLine.lean`, the source-connected bounded scanner, the full original arithmetic bounce chain, and Agent 15's first-return proof, then these new certificates. No trusted local stubs are used in CI.

## Exact theorems and mechanism

`SectionReachBridge.lean` develops a generic inductive theorem: for any deterministic partial transition `f`, injective section embedding, positive-time exact section map `g`, and proof that no intermediate positive time reaches another section state, every raw section reach has a `g`-orbit witness. The converse lifts each section step into a finite raw path. These lemmas are independent of Machine C.

`CFirstReach.lean` specializes that generic result to Agent 8's original-source `fastNext` and `fastTime`:

```lean
theorem c0_reach_iff_fast_section (a k : Nat) :
  BB6CLine.Reach (a,k,0) ↔
    ∃ m, BB6.Agent8Section.run
      BB6.Agent8ComputableC.fastNext m (some (5,1)) = some (a,k)
```

`SectionUnique.lean` establishes uniqueness of the returned section state for any two deterministic, exact, no-skipped-section maps on the same system. It accounts for both halting cases; it only needs equality of elapsed times when both maps return a section point.

`CSectionCoincidence.lean` combines Agent 8's `fastNext_first` and `fastNext_exact` with Agent 15's `section_no_early_c0`, Agent 46's `section_exact`, and positive duration. The final original-source theorem is:

```lean
theorem fast_scanner_eq_arithmetic (p : Nat × Nat) :
  BB6.Agent8ComputableC.fastNext p = BB6.Agent46.secNext p
```

This equality is for all synthetic and authentic `c=0` input pairs. Source CI reports ordinary Lean axioms only for the new theorems; no `sorryAx` or extra assumptions.

## Scope and prior work

Agent 15 had **already proved** the analogous genuine `c=0` reachability equivalence for the Agent 46 arithmetic `secNext` in [SectionReachEquivalence.lean](../agent15-c-halting/SectionReachEquivalence.lean), using [SectionFirstReturn.lean](../agent15-c-halting/SectionFirstReturn.lean). The latter was present before this investigation. Agent 8 already had a first-event scanning theorem in [CSectionComputable.lean](../agent8-c-total-section/CSectionComputable.lean). The contribution here is a source-verified *cross-implementation identity*, together with an independent generic completeness proof for the scanner. This is an integration/reusability improvement and does not exclude any new authentic halting target.

To advance the actual BB(6) decision, exploit this pointwise identity to transfer an **unbounded** genuine-root invariant between the two implementations, then close an infinite residual stopping family. Longer finite traces and repeat proofs of existing reachability equivalence are low priority.


## Universal section-duration bound and exact terminal clocks

[Source-level Lean CI 42523682069](https://github.com/FlareZ123/bb6/actions/runs/42523682069) verifies:
- `SectionTimeBound.bounce_time_le_double`: for all `k,c`, `(bounce k c).1 ≤ 2*c`;
- `SectionTimeBound.secTime_le`: for all `a,k`, `secTime (a,k) ≤ 4*k+5`;
- `CSectionTimeEq.fastTime_eq_secTime_of_some`: on any successful section return, `Agent8ComputableC.fastTime = Agent46.secTime`. Thus both independent implementations agree on exact elapsed calls along any nonhalting section orbit.

[Source-level Lean CI 42524366274](https://github.com/FlareZ123/bb6/actions/runs/42524366274) verifies the new arithmetic terminal-clock theorem in [CParamHaltTime.lean](CParamHaltTime.lean), using Agent 15's original terminal-seed definition and power identity. The complete even-middle seed formula is

```
(bounce k (haltSeed k n)).1 + 2*k + 5*n + 6 = 2^(n+1)*(k+4)
```

whenever `k%2=0`. It yields exact clock identities for both infinite stopping-section families:

- **Low:** if `k+3*m+4 = 2^(2*m+3)`, then `secTime (1,k)+10*m+11 = 2^(2*m+4)`.
- **High:** if `k+j+3*m+5 = 2^(2*m+2)*(j+3)`, then `secTime (2*j+3,k)+4*m+3 = 2*k`.

Combining the low equation with its parameter constraint gives the same uniform law `secTime+4*m+3=2*k` for both families. The time is measured in original `CLine.nextC` accelerated counter transitions; it is **not** the six-state Turing machine's raw step count. This supplies exact stopping suffix arithmetic, but it is independent of the unresolved authentic-root reachability condition.

Verification note: local development used minimal interface stubs for imported old theorems. Both cited GitHub Actions runs reconstructed all original imports and passed from the unchanged committed source. The new derived theorems have no `sorryAx` dependency and were kept in `im-results/` rather than claiming a publishable BB(6) solution.
