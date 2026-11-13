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

**Not yet compiled.** The latest CI run `43397116562` failed while compiling `M1EvenQ4Prefix.lean`. The latest source edits (including namespace scope, list-association, coordinate, and local `sideBit_append_after_local` repairs) were pushed after that run and have not yet been checked. Do not cite the attempted composition theorems as established results until a fresh Lean run passes and the `#print axioms` audit completes.

The most recent compiler diagnostics before those edits included:
- list-association/index normalization in the left-stream bridge;
- right-boundary coordinate normalization in the linear sweep;
- several finite `q4RightShape` cell proofs;
- helper scope for `sideBit_append_after`;
- later S1 endpoint list equalities.

No exact value for BB(6), and no new universal upper bound, has been proved here.

## Next actions

1. Run `.github/workflows/agent42-champion-terminal-source.yml` after the latest edits.
2. Resolve the remaining `M1EvenQ4Prefix.lean` errors before interpreting the suffix or root composition files.
3. Compile `M1EvenQ4Suffix.lean` and `TM63M1EvenRootComposition.lean`, and inspect their `#print axioms` output for `sorryAx`.
4. Only after a clean compile, update the human-readable root research map with the first source-certified m=1,n=6 stage. Keep this work in `im-results/` until it is a complete, independently publishable mathematical result.
