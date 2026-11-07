# #429 canonical first-return map

**Status:** Intermediate research artifact. This is a source-connected Lean formalization and computational reduction. It does **not** decide whether the blank-root orbit halts, and it does not establish a new BB(6) bound.

The source is the unchanged DeepMind Cryptids module at commit `c86f15861709b76042998c5211c7b2f83991621b`:

`BusyBeaver.BB6.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA`

## Canonical burst exit

For a high-level seed `J(u,w)`, the first branch is

`(u,w) ↦ (2u+3, w-2u-3)`

when `2u+3 ≤ w`. `burstExit u w` repeatedly applies exactly this branch until its guard fails. The recursion is total: every recursive call decreases the second coordinate by at least three.

Writing `burstExit u w = ((a,b),n)`, the formal theorems establish:

- `burstExit_spec`: the original first-branch iterator reaches `(a,b)` in exactly `n` steps, and the first-branch guard is false at the endpoint.
- `burstExit_formula`: `a+3 = (u+3)·2^n` and `2a+b = 2u+w+3n`.
- `source_burst_decomposition`: the unmodified upstream `highLevelNext` trajectory from `J(u,w)`, after `n+1` steps, is exactly the native transition from the burst endpoint.
- `sourceReturn_run`: `sourceTurnaround` is therefore a genuine variable-length first-return map, with no source transition omitted.

The canonical return map `sourceTurnaround` either returns the next seed or returns `none` at the halt gateway. Its exact halting criterion is

`2u+w+3n+13 = 4(u+3)·2^n`

where `n` is the unique maximal first-branch burst length computed by `burstExit`. This turns the prior existential burst-gateway equation into a total, executable return-map test for each seed.

## Return-seed image and gateway filter

Every successful return seed `(a,b)` satisfies:

- `b` is even and `b ≥ 2`;
- `a=0` or `a ≥ 6`;
- if `a=0`, then `b ≥ 10`.

This is a theorem about the entire image of the return map, independent of the initial seed.

For any even-`w` seed, a halt on its next burst requires `w ≡ 2 (mod 6)` and an odd burst length. The first exact blank-root returns are:

`(0,0) → (0,12) → (0,28) → (0,44) → (23,18)`.

The bursts starting at `(0,12)` and `(0,28)` are ruled out by the mod-6 condition. The first unshielded burst seed is `(0,44)`; its next return is exactly `(23,18)`. These are finite-prefix results only.

## Research significance and limitations

This contribution adds a canonical total first-return operator, a source-level decomposition theorem, a strict image restriction for successful return seeds, and a canonical mod-6 halt filter. It gives future work a clean object to analyze: iterate `sourceTurnaround` from `(0,12)`, and determine whether any return reaches the exact exponential gateway.

The image restriction and mod-6 filter do not prove that the blank-root orbit avoids or reaches the gateway. The synthetic prepared-input counterexamples reported elsewhere remain valid falsifiers of arbitrary local-window arguments; this result does not rely on such arguments.

## Verification

The core return-map files were checked locally with Lean 4.36.0-rc2. Pinned-source CI run 8 passed for the initial source-connected return map. The expanded mod-6 and blank-prefix corollaries in the current file are being rechecked in a follow-up run.

The source file includes `#print axioms` checks. The reported dependencies are only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or project-specific axiom is used.

## Next mathematical question

Analyze the induced return dynamics on the image set

`{(0,w) : w even, w≥10} ∪ {(u,w) : u≥6, w even, w≥2}`

and determine whether the blank-root orbit from `(0,12)` reaches the exact exponential gateway. Avoid another ungrounded finite-modulus or fixed-window exclusion; the next result must constrain the authentic return orbit itself.
