# Genuine blank-root predecessor tower for BB429 (Agent 18)

This is an intermediate research program for the unchanged source-equivalent BB429 accelerator, not a decision of machine #429 and not a BB(6) upper bound. The original raw six-state machine is `1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA`. The all-time root claims below concern the actual blank accelerator root `BB429.run n (0,0)`, using the exact `next` definition in `im-results/agent5-429-rank/BB429Rank.lean`.

## Three all-time congruence theorems

[BB429SevenStrong.lean](BB429SevenStrong.lean) proves, for every `n,a,b:Nat` and `BB429.run n (0,0)=some(a,b)`:

1. `a%8=7 → b%8∈{2,3}` (`rooted_seven_strong`).
2. `a%16=1 → b%8∈{1,2}` (`rooted_one_strong`).
3. `a%32=5 → b%8∈{2,4,5}` (`rooted_five_strong`).

These improve older source-certified individual restrictions from Agent39. Each strengthening has an exhaustive one-step Lean theorem `incoming_{seven,one,five}_strong` and an all-time blank-root theorem by induction on the exact accelerator time. The proof uses the genuine source step, not a finite screen or synthetic root.

The corollary `no_halt_five_mod32` excludes the terminal sector `a%32=5`; this sector was already ruled out by earlier Agent6 work. The other two predicates strengthen root structure but do not decide a surviving original-source halting sector.

## Branch-29 final-burst feeder

[NEGATIVE_DYADIC.md](NEGATIVE_DYADIC.md) contains the detailed arithmetic and signed-inverse analysis.

**Accepted source-connected result:** conditional on the exact branch-7 final-burst equation, the genuine blank-root theorem `BB429Branch29BurstFloor.rooted_branch29_final_burst_floor` excludes `18 ≤ n < 16255`. Its earlier manual source CI run [45121716046](https://github.com/FlareZ123/bb6/actions/runs/45121716046) succeeded with only standard Lean axioms. This is a necessary terminal-gate bound, not a halt/nonhalt decision.

**Unaccepted finite-range extension:** `BB429Branch29Prefix.lean` contains an adaptive dyadic cover intended to prove `n ≥ 128000127), and `BB429Branch29Source.lean` contains the corresponding original-source wrapper. The key `cover_one_million` computation and its source wrapper have **not** been accepted. The local manual workflow run [45416601834](https://github.com/FlareZ123/bb6/actions/runs/45416601834) was stopped by a runner shutdown before the Prefix module, with no compiler diagnostic. The original-source chain run [45124760705](https://github.com/FlareZ123/bb6/actions/runs/45124760705) also failed after about 57 minutes; its failed-job logs were unavailable (HTTP 404), so no Lean error was established. Do not report the stronger bound as source-checked. Do not rerun the unchanged expensive cover; optimize or split it only if that finite result remains useful.

## Signed inverse structure: parity and exact first-pair reduction

[Agent22's signed-drift analysis](../agent22-429-signed-drift/README.md) identifies the remaining difficulty: mixed infinite signed inverse paths are not excluded by the existing six Bad leaves. The exact hand derivation in [SIGNED_F_RUN_PARITY.md](SIGNED_F_RUN_PARITY.md) adds a structural restriction:

- Every maximal run of standalone (F)-blocks that is followed by another paired block has even length. Therefore every (F)-run on a hypothetical infinite path is even, using Agent22's theorem that such a path must contain infinitely many (F)-blocks and paired blocks.
- Modulo 4, the F-run length is (2) when the preceding and following pair types agree, and (0) when they differ (with the initial state treated as a virtual (S)-pair).

This is an exact congruence argument from the compressed transition rules, but it is **not yet formalized in Lean** and does not itself eliminate the mixed recurrent SCC. The derivation has been sent to Agent22 for integration or adversarial review.

The exact initial-state classification is recorded in [INITIAL_PAIR_CLASSIFICATION.md](INITIAL_PAIR_CLASSIFICATION.md): a first paired transition exists **iff** \(k\equiv2\pmod4\) or \(k\equiv15\pmod{16}\). In the first class the first pair is EF after four further F-blocks; in the second it is SF after six. For every other \(k\), the entire signed inverse path is the finite F-spine and terminates before any pair. Thus 11/16 of the branch-29 parameters are eliminated at the first paired-transition test. This is a theorem about the compressed signed system, not yet a Lean/source-root theorem.


## Why the root congruence tower works

The only possible incoming transitions to sufficiently large odd first counters are the first branch `(x,y)↦(2x+3,y-2x-3)` or the non-first odd-`y` branch `(x,y)↦(d+7,2y-4)`. In the first branch, congruence `a%8=7` forces even `x`, and true-root even8 forces `y%8=2`, hence output `b%8=3`. In the non-first branch, the target residue and source guard require `b%8=2`; the alternative would force an impossible odd second counter at a positive even true-root parent. The `a%16=1` and `a%32=5` cases reduce to the preceding root predicates. Lean splits every original `BB429.next` branch and invokes `omega` on the complete nonlinear-guard cases.

## Reproducibility and limits

The three root-strengthening theorems were locally checked on Lean 4.36.0-rc2 with axiom audits reporting only `[propext, Classical.choice, Quot.sound]`. The accepted branch-29 floor theorem was source-checked in CI as noted above. The newer million-prefix extension has no successful compiler or original-source audit. The local shell was unavailable in this invocation, so the CI shutdowns were not replaced by a local compile.

The real #429 root decision and the global BB(6) value remain open.

## Most valuable next work

1. Formalize the even-F-run lemma in Lean and incorporate it into the signed compressed-path analysis.
2. Use the even-run and pair-type constraints to attack the mixed recurrent SCC, ideally with a well-founded parameter-sensitive argument for the special line `b=2a-3`, `a=29-32c), `c=3k+4≥4`.
3. Only if the finite-range bound is still strategically useful, refactor its expensive cover into independently checked batches; do not repeat the unchanged long computation.
