# Machine C: executable full arithmetic stopping guards and a strictly new infinite phase sieve

**Research status, 7 November 2026:** this is an intermediate original-source Machine C reduction, not a six-state Busy Beaver value, a Machine C halting verdict or a blank-reachable stopping witness. Source authentication of the finite phase filter passed. The all-conjunct Boolean interface and infinite nonredundancy proof have local Lean checks; their complete original-source verification is tracked in the manual workflow below.

## Current mathematical target

The original blank-derived Machine C section run starts at `(5,1)` under the exact source `BB6.Agent46.secNext`. The latest integrated theorem `BB6.Agent24Phase.blank_halts_iff_c58_two_sided_all_phase` states an exact equivalence between original blank halting and the presence of at least one reachable member of either of two arithmetically parameterized stopping families. Its high sieve is

```lean
BB6.Agent11C58AllDepth.highAllowed j m ∧
  ¬ BB6.Agent46.allPhaseExcluded j m
```

The `allPhaseExcluded` predicate has an unbounded existential depth `r` syntactically, but includes `r+4≤2*m+2`. Unlike a fixed search horizon, that source condition gives a complete per-parameter finite search.

## A complete Boolean halting interface for each parameter

[StrongPhaseBool.lean](StrongPhaseBool.lean) supplies:

- `phaseExcludedBool_iff`: scanning all `r<2*m+1` is exactly equivalent to the original phase exclusion.
- `phaseGate_log_bound` and `phaseExcludedFastBool_iff`: every excluded depth also satisfies `r≤Nat.log2 (j+3*m+3)`. Thus the optimized scan `r<min (2*m+1) (Nat.log2 (j+3*m+3)+1)` loses no target.
- `phaseFast_equals_slow`, `highAllowedGuardedFast_iff` and `blank_halts_iff_joint_guarded_fast`: the fast filter is substitutable in the *actual original blank-root halting equivalence*, preserving all prior low/high conditions and the exact source fixed-target root decision.

The unmodified source build and Lean axiom audit **succeeded** for the slow filter [run 42344144374](https://github.com/FlareZ123/bb6/actions/runs/42344144374) and bitlength-optimized filter [run 42344586006](https://github.com/FlareZ123/bb6/actions/runs/42344586006). The audited central theorems use only standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

[FullBoolean.lean](FullBoolean.lean) additionally makes every old conjunct executable. Its explicit local `Decidable` dictionaries handle three previously unbounded dyadic quantifiers: Agent19's parity-dependent depth, Agent11's old C58 depth, and Agent24's new phase depth. The original historical predicates are unfolded in their exact hierarchical composition; ordinary modular guards and the original recursive `affineNormalize` are evaluated constructively. `highAllowedFullBool_iff`, `lowAllowedFullBool_iff`, and `blank_halts_iff_full_booleans` prove a complete rewrite of the halting criterion into Boolean predicates of each `m` or `j,m`. All three compiled with ordinary axioms in [source CI 42345491167](https://github.com/FlareZ123/bb6/actions/runs/42345491167), though that **overall run failed** on a separate sample `by decide` (Lean kernel could not reduce the deeply recursive source affine normalizer). The failed sample was removed; the full revised module awaits a final clean source check.

**Crucial scope:** the per-parameter computation and exact fixed-target rooted decision are finite. The two existential parameter domains remain *unbounded*, so no global Machine C halting decision or BB(6) bound has been established.

## Infinite strict separation from every previously integrated high sieve

[InfiniteStrict.lean](InfiniteStrict.lean) gives a constructed candidate family

```
j(t) = 2256 + 4096*t,
m = 15,
r = 8.
```

For every natural `t`, the proposed source theorems state

```lean
BB6.Agent11C58AllDepth.highAllowed (j t) 15
BB6.Agent46.allPhaseExcluded (j t) 15
¬ BB6.Agent24Phase.highAllowed (j t) 15
```

and `j(t)<j(t+1)`. Therefore the new all-phase gate strictly deletes infinitely many distinct high stopping parameter pairs admitted by the *entire* previous integrated C58, ValSix, and old dyadic conjunction, rather than merely by one selected old subfilter.

The proof handles all previous restrictions directly: the old Agent19 parity gate requires odd depth at this odd-left residue, whereas `j+3m+3=256*(9+16t)` has exactly 2-adic valuation eight; the old C58 gate cannot hold because `j+9m+14` is odd. All finite historical residue conditions are discharged algebraically. The difficult affine-normalizer conjunct is evaluated *symbolically at all t* in [AffNormFamilySource.lean](AffNormFamilySource.lean), which proves seven exact forced source normalizer steps to a terminal pair with right counter `137438953440*t+75799461868`, never four. The new phase exclusion is witnessed at `r=8` by

```text
j ≡ 0 (mod 16),
j + 3m + 3 ≡ 9·2^8 (mod 2^12).
```

A genuine original-source upgrade, [TrueStoppingFamily.lean](TrueStoppingFamily.lean), proves the corresponding counter `k(t)=2^32*(j(t)+3)-(j(t)+50)` satisfies `secNext (2*j(t)+3,k(t))=none` and is *not* reachable from the blank origin. This makes the strict family a family of physically legitimate stopping inputs, rather than arbitrary syntactic pairs. Its nonreachability follows from the source cone already proved by Agent24; no individual difficult-root decision is claimed.

This infinite-family formalization passed a locally reconstructed Lean4.36.0-rc2 source-shape test, **not yet a completed original-source proof** at the time of writing. Validation will require the exact `Agent15.affineNormalize`, all original high sieve definitions, the original SectionParam stopping theorem and the source all-phase exclusion, with successful original-source CI at the committed SHA.

## Original-source verification

The existing **manual-only** [agent24-c-strong-phase workflow](../../.github/workflows/agent24-c-strong-phase.yml) compiles the unchanged upstream section transition, exact inverse, blank-root bridge, historical high gate modules and the new theorem files. No new workflow was created. Source checks must end with successful Lean kernel compilation and `#print axioms` without `sorryAx`. The earlier source-authentic integrated [Agent24 result run 42336609896](https://github.com/FlareZ123/bb6/actions/runs/42336609896) succeeded.

Older failed runs and their resolution: 42344916913 hit a `Decidable` typeclass synthesis failure from unfolding the entire nested high sieve at once; the module now builds each original named `Decidable` instance in dependency order. 42345491167 fully compiled the Boolean theorem statements and clean axiom audits but the separate numerical example failed because `by decide` did not reduce the source normalizer. A symbolic source proof replaces numerical reduction.

The unresolved next milestone is an *all-parameter* theorem excluding the remaining blank-reachable stopping events, or an authentic halting witness. Another finite parameter sample, alone, cannot settle this quantifier.
