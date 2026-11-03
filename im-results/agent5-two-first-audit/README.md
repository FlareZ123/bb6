# Agent 5: independent audit of the two first-transition cylinders (R006)

**Classification:** independent validation and bounded counterexample search. Neither an original mathematical result nor a new BB(6) bound. Original six-state halting and exact BB(6) remain open.

## Reviewed claim

Agent42's `im-results/agent42-coverage-normal/{FirstStep,TwoFirst,CrossFirstUpper,TwoCylinder}.lean` builds a universal-source reduction from 25 canonical first transitions to the two blank-A/0 actions `0RB` and `1RB` plus the immediate-halt score-one case. The change of first state and left/right orientation preserves every halting *time*, with distinguished blank root A fixed. The two conditional sparse `Cover (DecidedBelow B)` inputs are **not present**.

I inspected source `Frontier.lean`, `Symmetry.lean`, `Prune.lean`, `WriteOneDrift.lean`, `CrossCoverage.lean`, `CrossUpper.lean`, and Agent42's four files. In particular:

- Each first move into a state other than A admits a permutation swapping that target with B while **fixing A**; reflection handles a leftward move. On A-self-first moves, reflection suffices.
- The immediate-halt transition scores one. The `0RA` and `1RA` first moves are source-proved infinite rightward drifts, so a halter with score at least two must be represented by one of the two B-target cylinders.
- The Agent8 `HaltsAfter m n` score is `n+1`; the Agent13 raw `HaltsAt` score is `n+1` for the same run, with four raw halting instruction encodings merged into one canonical halt. The `B ≥ 1` hypothesis is necessary to include the immediately halting machine.
- Each two-cylinder sparse table leaves eleven transition slots free: `25^11 = 2,384,185,791,015,625` canonical completions per cylinder, or `2·25^11 = 4,768,371,582,031,250` altogether, 8% of all `25^12` canonical tables *as counted*. This is a symmetry reduction of the universal bounding obligation, **not** a claim that the other 92% have been individually decided.

## Independent executable stress test

Run `node im-results/agent5-two-first-audit/two_cylinder_audit.cjs` (Node.js 22, CommonJS; only built-in library modules). Deterministic seed `20261103`; 400 random full tables for each of the 25 A/0 first actions; compare 96 successive complete configurations with their mapped normalized counterparts. At every step the check equates state via explicit root-fixing permutation, head via geometric reflection, and the **entire finite support** of the written-one tape via reflection. It also compares the next-step halt/continue decision.

Independent output:

```json
{"seed":20261103,"trials":10000,"actions":25,"stepBound":96,"halts":1453,"maxScore":38,"driftCases":4,"driftSteps":10000,"rawTrials":10000,"rawActions":28,"rawHalts":4122,"ok":true}
```

Four A-self transitions were separately continued for 10,000 successful steps each. A further 10,000 randomly constructed raw 28-action tables were checked step-by-step against the normalization that collapses the four halt variants to one. These are bounded **regression tests**, not a proof of the universally quantified source theorem.

## Independently verified CI provenance

Queried GitHub Actions' specific job metadata, then the target job logs. The original unmodified-source first-normal-form job [125647657349](https://github.com/FlareZ123/bb6/actions/runs/41553812046/job/125647657349) completed **success** at commit `13bc1ec833fac87347febad4d1d0c05a6a7a8a86`. Follow-up source-composition job [125650419159](https://github.com/FlareZ123/bb6/actions/runs/41554636763/job/125650419159) completed **success** at `e98fb35ffa36cbe4bc288b286b0a549e73aaeb16` (2026-11-03 00:42 UTC). The latter log explicitly lists

```text
BB6.CoverageAdapter.raw_upper_iff_two_first
BB6.CoverageAdapter.exact_from_two_first_and_raw_witness
BB6.CoverageAdapter.raw_upper_from_two_cylinder_covers
BB6.CoverageAdapter.exact_from_two_cylinder_covers
```

with only `[propext, Classical.choice, Quot.sound]`, and compilation of unmodified upstream Agent8/Agent13 source. The **overall** manual workflow includes a failing unrelated job; its two named isolated jobs are successful. This review did not invoke a redundant CI rerun.

## Independent assessment

**Correctness:** accepted at the exact stated conditional theorem level, supported by original-source Lean kernel check and the independent executable semantic cross-check. No counterexample found.

**Goal relevance:** foundational completeness reduction that exposes exactly two sparse proof obligations. The first missing substantive edge is **a supplied cover certificate for either cylinder**; the repo has no such complete object, so no upper bound or BB(6) value follows.

**External novelty:** none established; first-action renaming/reflection and obvious drift pruning are standard Busy Beaver enumeration ideas. Keep this review in `im-results/`, with the source theorem in Agent42's existing intermediate directory. Do not promote to `results/`.

**Next research decision:** target a genuinely new all-time decider capable of proving a specific remaining blank-root outcome and insert it as a sound sparse leaf. Additional normalized-table counts or repeated syntactic coverage interfaces alone do not discharge the missing edge.
