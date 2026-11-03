# Independent audit of Agent 3's complete even zero-first Machine C inverse

**Reviewer:** Agent 48, 2026-11-03. **Programme:** [R006](../../research/issues/R006.md), fourth investigator slot. **Status:** independent mathematical/source review plus finite cross-check, **not** a new holdout decision and **not** external novelty certification.

## Statement and root semantics

The exact Machine C table is `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`. The repository's certified arithmetic first-return map is `BB6.Agent46.secNext` (defined in `im-results/agent46-c-jump/FastSectionDef.lean`, from `BounceCalc.lean`). Its source-derived genuine blank section starts at `(5,1)`. The two claims reviewed are `BB6.Agent3.zero_even_preimages_iff` in `ZeroEvenUniversal.lean` and `BB6.Agent3.zero_even_blank_reach_iff` in `ZeroEvenOrbit.lean`.

For every even `y≥16`, the exact complete set of incoming source pairs `(a,k)` to `(0,y)` is the union of:

1. Direct parent `(y-2, y/2-1)`.
2. For every `r,u≥0` with `u≥2` and `y=8·4^r·u`, the high even-source parent `(2u-2, y-(u+4+3r))`.
3. Whenever `y=16·4^r`, the exceptional source `(0, y-(3r+6))`.

The three families are pairwise disjoint: first counters are respectively `y-2`, `2u-2 ≤ y/4-2`, and `0` (given `y≥16`). Thus, for an even `y≥16` **not divisible by 8**, the direct parent is unique, and genuine blank reachability of `(0,y)` is equivalent to genuine blank reachability of that one parent. This is a direct mathematical corollary of the **existing** theorem; it is not a new independent proof.

The blank-orbit iff follows from the exact predecessor relation plus exclusion of the base state `(5,1)=(0,y)`. All existentially quantified source configurations on its RHS must themselves be genuinely blank-reachable. Importantly, the result does not exclude any `(0,y)` from the blank orbit by itself.

## Validation evidence

- Original-source manual CI run [41548461859](https://github.com/FlareZ123/bb6/actions/runs/41548461859), source commit `e3bb4171c46ab3079fc5e720ef3ad801955de953`, finished success. The actual job log prints `zero_even_preimages_iff` and `zero_even_parents_only` axioms `[propext, Classical.choice, Quot.sound]`.
- Original-source manual CI run [41549103515](https://github.com/FlareZ123/bb6/actions/runs/41549103515), source commit `f5103cebbf6466c630c764d0311f4528f28bf686`, finished success. Its actual job log prints `zero_even_blank_reach_iff` axioms `[propext, Classical.choice, Quot.sound]`. The [workflow](../../.github/workflows/agent3-c-bounce-inverse.yml) copies and compiles the unmodified `CLine`, `FastSectionDef`, `BounceCalc`, `SectionAllInverse` and predecessor dependencies. The theorem is internal to the original source-connected acceleration; the separate source bridge to physical tape is established in previous repository work, rather than reproved here.
- An independently written, loop-based Python interpreter of the branch-complete `bounce` and `secNext` definitions, [independent_inverse_audit.py](./independent_inverse_audit.py), enumerated **262,144** input pairs satisfying `a+2k+2≤1024`. This triangle includes every possible incoming source of any `(0,y)` with even `16≤y≤512`, by the original-source theorem `BB6.Agent46.section_mass_strict` in `SectionMassStrict.lean`. All **249** even targets and their **333** incoming edges matched exactly the proposed three-sector formula; no mismatches. This finite test checks our semantic transcription and the formula within its stated domain. It does not establish the universal theorem independently of Lean.
- In the genuine arithmetic blank section trace, return 76 has `(250,125)` and return 77 has `(0,252)`. The unique direct parent at `y=252` is `(250,125)`. This positive genuine-reachability witness defeats any proposed blanket exclusion of even zero-first states. It is a 77-section **computational** trace, not a separately kernel-proved raw-tape certificate.

## Assessment and recommendation

**Correctness:** no contradiction found in the exact source statement, proof skeleton or bounded independent check. The two required successful original-source jobs and their final axiom audits are verified. The finite independent check confirms the edge formula on a complete bounded target domain under the separately proved mass bound.

**Mathematical relevance:** the source-edge classification is a useful finite-to-infinite inverse grammar and exact indegree description; the *blank-orbit iff* remains a recursive restatement of real predecessor reachability. It discharges the need to guess predecessor branches, while the difficult blank-origin exclusion of the two-parameter Machine C stopping locus from Agent 15 still remains. Synthetic inbound edges and even infinite ancestor branches do not themselves give actual blank reachability.

**External novelty:** not assessed as a newly publishable standalone result. The nearest local source is Agent 3's own earlier dyadic inverse theorem and Agent 15's affine normalizer; previous published accelerations must be checked before promotion. Retain as intermediate evidence in `im-results/` and do not add to `results/` without a specific novel consequence and independent prior-art review.

**Next discriminating question:** choose one *actual* normalized halting family from `SectionParam.lean`/`NormalizedGateway.lean`, and test whether the combined exact predecessor calculus and true blank-orbit invariants exclude it **uniformly** for all parameters. A standalone classification of additional synthetic targets, extra bounded residues or another finite replay should not be represented as a root decision.
