# A total source-connected forced inverse normalizer for BB429

Agent 1, 2026-11-04. **Original unchanged repository-source Lean verification succeeded at [CI 41875237250](https://github.com/FlareZ123/bb6/actions/runs/41875237250)** in Lean 4.36.0-rc2 for a general theorem about *every* natural pair `(a,b)`. Additional transport into the unchanged original DeepMind Cryptids high-level machine is under [native source CI in the agent1-429-native-86 workflow](../../.github/workflows/agent1-429-native-86.yml), and should not be treated as full original upstream verification until that job succeeds. This is a reusable intermediate result; it does not decide the halting problem of any entire machine or BB(6).

## The algorithm

The original #429 accelerated transition is `BB429.next` from [Agent 5](../agent5-429-rank/BB429Rank.lean). Its strictly increasing rank is `2*a+b`. The new total `forcedNormalize a b` repeatedly replaces the target as follows:

1. If `a≥13`, `a%2=1` and `b%8≠2`: replace `(a,b)` with `((a-3)/2,b+a)`. For a target actually reached from the blank root, Agent6's `admissible_odd_predecessor` proves that all other incoming branches are impossible after applying the source-certified even-root parity invariant. The explicit source transition back to the target is also proved.
2. Otherwise if `a≥6`, `a%2=0` and `b%4=2`: replace `(a,b)` with `(a-3+(b-2)/4,b/2)`. A new exact source case split proves this is the **only** incoming transition into any such positive even target, and its reverse source step is valid.
3. Otherwise return `(a,b)`.

Every first rule lowers rank `2*a+b` by exactly three; every second rule lowers it by exactly seven. Lean accepts the definition's genuine `termination_by a b => 2*a+b` proof, which covers all natural numbers without artificial search depth or loop cutoffs.

## Formal theorem

```lean
BB429ForcedNormalize.blank_reach_iff_normalized (a b : Nat) :
  (∃ n, BB429.run n (0,0)=some (a,b)) ↔
  (∃ n, BB429.run n (0,0)=some (forcedNormalize a b))
```

This is a **two-way exact existential reachability equivalence**, proved by strong induction on the strict rank, including all exceptional or small states. It does not assume a bounded orbit time, a known root visit or a stopping predicate. The complete [Lean source](BB429ForcedNormalize.lean) is imported from genuine `BB429Rank`, `BB429LowOddMod8`, and `BB429No381mod1024`, with proof kernel checked against the actual repository files.

A separate total executable Boolean filter `forcedExcluded a b` checks whether the fully normalized residual has strictly positive even first coordinate and second coordinate different from two modulo four. The corresponding theorem proves:

```lean
BB429ForcedNormalize.forcedExcluded_sound (a b : Nat) :
  forcedExcluded a b = true →
  ∀ n, BB429.run n (0,0) ≠ some (a,b)
```

This filter is deliberately **sound but incomplete**. Returning false supplies no evidence of reachability or halting.

The [source-native transport](SourceForcedNormalize.lean) uses the previously source-certified exact two-way source simulator `BB429SourceLadder.source_run_eq` and has an upstream original Cryptids `source_blank_reach_iff_normalized` theorem plus `source_forcedExcluded_sound`. [Native CI workflow](../../.github/workflows/agent1-429-native-86.yml) compiles it with the original SHA-pinned upstream source and full dependencies; consult the actual run status.

## Practical implications and limitations

This reusable normalizer yields a single kernel-verified theorem for infinitely many states and a mechanized way to reduce arbitrary rooted reachability questions before performing more expensive complete inverse splits. It handles the predecessor first-branch and positive-even exact-inverse cases without collecting an ever-growing list of manually coded residue-specific lemmas.

For odd targets with `b%8=2`, the algorithm intentionally stops because non-first predecessors may be source-admissible. A complete handling of those bifurcations, tied to a blank-root invariant or a finite arithmetic well-founded strategy, is a promising next step toward eliminating an entire unresolved #429 stopping sector. This normalizer alone does not settle whether any of the surviving 86/2048 original raw terminal classes is reachable. It must not be promoted as a new BB(6) value or an entire machine decision.

No external mathematical novelty assessment has yet been completed. Preserve the source and CI evidence under `im-results/` pending comparison with earlier techniques.
