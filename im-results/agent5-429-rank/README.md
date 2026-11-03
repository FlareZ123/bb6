# Agent 5: a rank and partial arithmetic shield for BB(6) Cryptid #429

**Status:** mathematically proved properties of an exact, self-contained transcription of a published high-level transition map, independently checked against the raw machine on finite cases. **Intermediate result, no complete blank-tape halting decision, no new BB(6) bound.** Registered as targeted R001 research.

## Exact source and scope

Six-state, two-symbol rooted machine:

`1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`

The original [Google DeepMind Cryptids Lean module at pinned commit `c86f15861709b76042998c5211c7b2f83991621b`](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA.lean), blob SHA `1ce1cc5d15c943cc9766e0780a859de64d2e9873`, contains a formally certified acceleration `highLevelNext` acting on `J(u,w)` starting at `J(0,0)`. Its source includes `isHalt_iff_highLevel_acceleration`. Our [standalone Lean proof](BB429Rank.lean) defines the *same 12-case arithmetic map* using `Nat × Nat`, with branch order and natural-number truncation matching that pinned original.

**Evidence boundary:** Lean compiled and audited this exact standalone arithmetic transcription locally with **Lean 4.36.0-rc2**; we independently checked the raw-to-macro bridge on 18 finite examples. We have **not** kernel-compiled an import theorem identifying the standalone definition with the original upstream definition. The source relationship is audited textual equivalence plus original upstream proof and finite independent regression tests, not a newly kernel-checked cross-module adapter. The upstream acceleration is prior work; do not count it as our discovery.

## Proved statements

Let `T(u,w)` be the source two-counter map and `P(u,w) = 2u+w`.

1. **Strict rank, exact global interval.** If `T(u,w)=some(u',w')`, then
   `P(u,w)+3 ≤ P(u',w') ≤ P(u,w)+31`. The possible increments by branch are `3,16,23,12,10,20,10,5,31,11,7`; no continuing branch lowers rank.
2. **All-time consequences.** If the `n`th successful iterate reaches `t` from `s`, then `P(s)+3n ≤ P(t) ≤ P(s)+31n`. A positive-time recurrent accelerated state is impossible. To decide if a *particular fixed* target `t` is ever reached, it suffices to inspect `0≤n≤⌊P(t)/3⌋`. This is a parameter-dependent finite bound, not a uniform halting-time bound for the machine.
3. **Exact halting gateway.** `T(u,w)=none` if and only if `w+1=2u` (necessarily `u≥1`).
4. **A finite-state mod-6 shield for a single burst.** Define the protected residue set as the 18 pairs (`u mod 6,w mod 6`) described by:
   - Any `u mod 6` when `w mod 6∈{0,4}`;
   - `u mod 6=1`, `w mod 6∈{3,5}`;
   - `u mod 6=3`, `w mod 6∈{1,3}`;
   - `u mod 6=5`, `w mod 6∈{1,5}`.

   This set is closed under every **first-branch** transition `(u,w)→(2u+3,w-2u-3)` when `w≥2u+3`, and is disjoint from the halting line. Consequently, **for every** seed with even `w` satisfying `w mod 6∈{0,4}`, *an arbitrarily long run of first-branch transitions plus the first exit transition cannot halt*. This removes **two thirds of the three even-`w` seed residue classes** for that *one burst*, independent of `u`.

There is **no global shield**: the other source branches need not preserve the 18-pair invariant, and the actual orbit repeatedly starts bursts with `w mod 6=2`. The surviving class remains a hard infinite arithmetic target.

Proof declarations are `next_rank_interval`, `run_rank_bounds`, `no_positive_loop`, `reach_target_iff_bounded`, `next_none_iff_halt_line`, `shield_survives_first`, `shield_excludes_halt`, and `two_thirds_first_burst_safe`. Lean's `#print axioms` uses only standard kernel foundations `propext`, `Classical.choice`, and `Quot.sound` where needed, never `sorryAx`.

## Reproducible independent test

Run `node im-results/agent5-429-rank/BB429RankTest.cjs` (Node CommonJS, built-in assertions) and compile `im-results/agent5-429-rank/BB429Rank.lean` using the **supplied Lean 4.36.0-rc2**. These tests were executed locally against the exact files that were committed: Git blob SHA of Lean `5a93ba2d833ca375478f1183f45712a34f299f19`, Node test `4c3a8ad618d86909ed41ef36fb939714e1462177`. The raw machine is initialized with a fully blank tape, and after precisely **35 primitive transitions** has the source's junction configuration `J(0,0)`; the checked head is at coordinate 3 with nine written-one cells relative to head `{-6,-5,-4,-3,-2,-1,0,1,3}`.

The independent checker validates:

- 500,000 deterministic arithmetic test inputs for rank, gateway equivalence, and shield preservation;
- 18 explicit raw primitive-simulation cases `J(u,w)→J(u',w')` or primitive halting, including `J(0,0)→J(0,12)` in 110 primitive steps and `J(1,1)` halting after 41 primitive steps;
- an independent exhaustive mod-6 orbit check of every protected even-`w` seed residue;
- a blank-origin 3,000,000-step **accelerated** trajectory with no macro halt. The 231,035 post-turnaround seeds split as `w mod 6=0: 86,549`, `2: 89,092`, `4: 55,394`. Exactly 141,943 seeds, about **61.44% of the observed sample**, are in the protected seed classes. The proven two-thirds figure concerns residue classes, not this sampled frequency.

For full transparency, these finite empirical observations add no new blank-orbit bound beyond upstream work, which already reports simulations to approximately `2.16×10^17` primitive steps. Finite tests cannot establish indefinite nonhalting.

## Research significance and next attack

The source's first-branch orbit doubles `u` while the strict rank increases by only 3 per step. Its halting line is a shrinking-turnaround target. The mod-6 certificate supplies a uniformly valid prune at *each individual burst*. A serious next step would derive an all-time invariant on post-turnaround seed residues or an exact first-return map and prove that the unshielded `w mod 6=2` seeds cannot satisfy the gateway. Existing DeepMind source explicitly classifies #429 as heuristically likely halting, so a global nonhalting claim would require substantially new evidence.

No publication-level novelty was established relative to all prior literature; this is kept under `im-results/`. It is a reusable verified arithmetic starting point, and it does **not** alter `results/README.md`.
