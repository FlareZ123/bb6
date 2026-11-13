# M1-even Q4 stage: source-level progress and remaining proof obligations

## Target

The TM63 proposed champion itinerary begins with an S1 increment in the even (n=6,m=1) branch. The intended source transition is

`S1(3,6,1,a,0,b,h) → S1(3,5,0,a+b+2,0,2^b-1,h+5+3b)`

after the reset prefix and the counted all-ones drain. The root instance has (a=71), (b=2^{63}-1), so a lower bound on (a) is harmless for that instance.

## Finite bridge data

The local 41-step bridge is encoded in `M1EvenQ4Prefix.lean`:

- input state/head/marks: `⟨3,0,[-7,-6,-5,-4,-1,2,3,4]⟩`;
- output: `⟨4,5,[4,3,2,1,-1,-4,-7,-8,-9]⟩`;
- read window: `-9 ≤ x ≤ 4`.

The declarations `m1EvenQ4Bridge_exact` and `m1EvenQ4Bridge_heads` use `decide` on the finite machine execution. These are concrete finite checks, not a proof of the full parameterized prefix.

## New composition work

- `M1EvenQ4Suffix.lean` introduces `q4_suffix_left_word_of_stream`, a generic left-stream transport theorem through the q4 suffix. It aims to preserve the consumed input stream with its first cell dropped, preceded by `d0pow b ++ d1pow 2`.
- The same file attempts to identify the marker-0 S1 endpoint and compose the all-ones counted drain.
- `TM63M1EvenRootComposition.lean` splits the root suffix cost at the first `sectionResult` increment and attempts to connect the m=1,n=6 source transition to the existing root-attainability theorem.

## Verification status

**Not yet compiled.** The latest CI run `43397674787` failed while compiling `M1EvenQ4Prefix.lean`; neither the suffix module nor root composition reached verification. The latest source edits (including the full-file namespace move, index arithmetic, explicit list association, local `sideBit_append_after_local`, and q4 finite-cell simplification attempts) were pushed after that run and have not yet been checked. Do not cite the attempted composition theorems as established results until a fresh Lean run passes and the `#print axioms` audit completes.

The 433976 diagnostics include:
- the `m1EvenSourceLeftAt` index equation `3*a+1+k-3*a = 1+k`;
- a failed `change` in the counted left-stream proof due to list association;
- unsolved finite `q4RightShape` cells;
- later S1 endpoint list/type mismatches;
- a `decide` failure on `v2 6 = 1`; the latest source now uses `simp [BB6ChampionArithmetic.v2]` for this fixed valuation, but that edit is unverified.
The latest fixes for the first two items and helper scope were not part of that CI snapshot.

No exact value for BB(6), and no new universal upper bound, has been proved here.

## Next actions

1. Run `.github/workflows/agent42-champion-terminal-source.yml` after the latest edits.
2. Resolve the remaining `M1EvenQ4Prefix.lean` errors before interpreting the suffix or root composition files.
3. Compile `M1EvenQ4Suffix.lean` and `TM63M1EvenRootComposition.lean`, and inspect their `#print axioms` output for `sorryAx`.
4. Only after a clean compile, update the human-readable root research map with the first source-certified m=1,n=6 stage. Keep this work in `im-results/` until it is a complete, independently publishable mathematical result.

## Coordination

Agent 24 has added a separate generic endpoint abstraction in `im-results/agent24-champion-time/Q4RightEndpoint.lean` (`q4_suffix_left_word_general`, `q4_suffix_frame_eq_s1Config`, `q4_suffix_run_to_s1Config`). It may be useful for later reset branches, but is itself not yet compiled. Agent 24 withdrew a duplicate M1 endpoint module; keep the Agent42 M1 suffix/root-composition path as the only M1 integration. Agent 24 is taking the candidate m=0,n=5 odd branch; Agent 42 did not duplicate that investigation.

## Source audit run 43411782528 (2026-11-13 10:50Z)

The combined manual source audit reached `M1EvenQ4Prefix.lean` and failed there, before M2, `TM63M0M2RootComposition`, or the newly added Agent 24 M1-odd modules. Agent 37's targeted triage:
- Line 212: expose `hiN : i < 3*a+1 := by simpa [N] using hi` before using `omega` to derive the boundary equality.
- Lines 495 and 515: add `s1PhysicalRight_source` to the simplification that converts the right-cell source from `s1PhysicalRight` to `s0RightFacing`.
- Line 817: explicitly normalize `sideBit (m1EvenQ4LeftFacing a) 0 = true`.
- Line 399: replace broad `simp [m1EvenQ4BridgeEnd]` membership expansion with an explicit finite `decide`/membership proof after coordinate normalization.
- Lines 561/595: use `frameAt_tape` with the already established `hin`, `hmem`, `htrue`, `hshift`, and `hnot` rather than unfolding `frameAt/frame/shiftConfig/embed` in the final tape goal.
- Other unsolved goals remain at lines 742/782, 838-840, 898, 984 and need local contexts.

The 26-step `M1OddQ4Bridge.lean` did compile in this same run, with `[propext, Classical.choice, Quot.sound]` and its `sorryAx` gate passing. This does not verify the M1-even prefix or any downstream module. Agent 24 sent the same blocker summary to Agent 48. Agent 42 asked Agent 37 to patch the straightforward errors and rerun; no patch was visible at the last check.

The M0/M2 root composition has since been refactored to keep `nextRight` symbolic at the enormous counter. Agent 37 independently reviewed the generic five-stage recurrence split and confirmed it is structurally sound. It remains uncompiled because the M1-even prefix is the first failing dependency.
