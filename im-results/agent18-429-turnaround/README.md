# #429 canonical first-return map

<badge>Intermediate research artifact</badge>

## Status

This is a source-connected, Lean-checked reduction of the pinned DeepMind Cryptids high-level acceleration for machine #429. It does **not** decide whether the blank-root orbit halts, and it does not establish a new BB(6) bound. It is intended as reusable infrastructure for the unresolved root-orbit problem.

The source is the unchanged Cryptids module at commit `c86f15861709b76042998c5211c7b2f83991621b`:

`BusyBeaver.BB6.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA`

## Construction

For a high-level seed `J(u,w)`, the first branch is

`(u,w) ↦ (2u+3, w-2u-3)`

when `2u+3 ≤ w`. `burstExit u w` repeatedly applies exactly this branch until its guard fails. The recursion is total: each recursive call decreases the second coordinate by at least three.

Write `burstExit u w = ((a,b),n)`. The formal theorems establish:

- `burstExit_spec`: the original first-branch iterator reaches `(a,b)` in exactly `n` steps, and the first-branch guard is false at the endpoint.
- `burstExit_formula`: `a+3 = (u+3)·2^n` and `2a+b = 2u+w+3n`.
- `source_burst_decomposition`: the unmodified upstream `highLevelNext` trajectory from `J(u,w)`, after `n+1` steps, is exactly the native transition from the burst endpoint.
- `sourceReturn_run`: `sourceTurnaround` is therefore a genuine variable-length first-return map, with no simulated branch omitted.

The canonical return map `sourceTurnaround` either returns the next seed or returns `none` at the halt gateway. Its exact halting criterion is

`2u+w+3n+13 = 4(u+3)·2^n`

where `n` is the unique maximal first-branch burst length computed by `burstExit`. This turns the prior existential burst-gateway equation into a total, executable return-map test for each seed.

Every successful return has a constrained shape:

- its second coordinate is even and at least 2;
- its first coordinate is either 0 or at least 6;
- if the first coordinate is 0, the second coordinate is at least 10.

The blank-root seed has first return `J(0,12)`.

## Research significance and limitations

The original high-level map is already a powerful acceleration. This contribution adds a canonical total first-return operator, a source-level decomposition theorem, and a stricter image restriction for successful return seeds. It gives future work a clean object to analyze: iterate `sourceTurnaround` from `(0,12)`, and determine whether any return reaches the exponential gateway.

The image restriction is a theorem about the return map's entire image, not an empirical observation. It does not prove that the blank-root orbit avoids or reaches the gateway. The synthetic prepared-input counterexamples reported elsewhere remain valid falsifiers of arbitrary local-window arguments; this result does not rely on such arguments.

## Verification

The files in this directory were checked locally with Lean 4.36.0-rc2. The pinned-source CI audit should be run with:

- dependency: `im-results/agent5-429-rank/BB429Burst.lean`
- extra dependency: `im-results/agent18-429-turnaround/BB429TurnaroundCore.lean`
- bridge: `im-results/agent18-429-turnaround/BB429TurnaroundSource.lean`

The source proof includes `#print axioms` checks. The reported dependencies are only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or project-specific axiom is used.

## Next mathematical question

Analyze the induced return dynamics on the image set

`{(0,w) : w even, w≥10} ∪ {(u,w) : u≥6, w even, w≥2}`

and determine whether the blank-root orbit from `(0,12)` reaches the exact exponential gateway. Avoid another ungrounded finite-modulus or fixed-window exclusion; the next result must constrain the authentic return orbit itself.
