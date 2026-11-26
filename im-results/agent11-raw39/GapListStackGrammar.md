# Raw39 1LE F1 siblings: gap-list orbit and candidate stack grammar

**Status: experimental / proof-pending.** This note concerns the three remaining 1LE siblings 5777, 5779 and 5787. It does not establish nonhalting, and it must not be promoted to `results/` until the macro return and invariant are proved.

## Boundary encoding

At the observed state-F, symbol-0 boundary, the left tape is exactly `00`. Encode each right-tape zero gap by

`gap(g) = 0^g 11`.

The right tape is a concatenation of these blocks. After the common initial prefix, the observed boundary orbit alternates:

- P phase: `[1,5] ++ W  ->  [3,1,2] ++ W`
- Q phase: `[3,1,2] ++ W  ->  [1,5] ++ f(W)`

The P phase takes 70 primitive steps on the sampled orbit and leaves the tail unchanged. The Q phase is more complicated; its cost depends on the tail and on the F1 completion.

The three tables differ only at F1:

| Residual | F1 action |
| --- | --- |
| 5777 | `0RC` |
| 5779 | `0RE` |
| 5787 | `1RC` |

For the first 20 Q phases, the simulator produced the same output (f(W)) for all three variants. Their primitive costs differ when F1 is visited. The first examples are:

| Input tail (W) | Common output (f(W)) | Q cost: 5777 / 5779 / 5787 | F1 visits |
| --- | --- | ---: | ---: |
| `[1]` | `[5,1]` | 150 / 150 / 150 | 0 / 0 / 0 |
| `[5,1]` | `[3,1,1,1]` | 118 / 118 / 118 | 0 / 0 / 0 |
| `[3,1,1,1]` | `[3,5,5,1,1,1]` | 318 / 310 / 306 | 2 / 2 / 2 |
| `[3,5,5,1,1,1]` | `[3,3,1,1,5,1,1,1]` | 142 / 142 / 142 | 0 / 0 / 0 |
| `[3,3,1,1,5,1,1,1]` | `[3,3,5,1,1,5,5,1,1,1]` | 452 / 448 / 444 | 3 / 3 / 3 |

These are exact outputs of the finite simulator, not a proof that every grammatical input returns. In the first 20 Q phases, F1 visits occur only on even-indexed phases from index 2 onward; the output tails remain identical across the three completions.

Reproduce the experiment with [`gaplist_orbit.py`](gaplist_orbit.py). It checks both P and Q boundary returns, verifies that P preserves the tail, and rejects any divergence among the three Q outputs.

## Candidate run grammar

Classify a gap (g) as:

- **X-gap** when (g\geq 3) (observed values 3 and 5);
- **Y-gap** when (g\leq 2) (observed values 1 and 2).

Group consecutive gaps of the same class into runs, weighting a run by the sum of its gap values. The observed tails after the initial `[1]` have the form

`X-run · (Y-run · X-run)* · trailing-Y-run`.

Equivalently, each such tail is a candidate `Core ++ Y^+` word, where `Core` consists of alternating nonempty X-runs and Y-runs and ends in an X-run. Every X-run has weight at least 3 (the terminal one at least 2); every Y-run is nonempty. The initial tail `[1]` is a separate all-Y base case.

Examples:

- `[3,3,1,1,5,1,1,1]` parses as X-weight 6, Y-weight 2, X-weight 5, trailing Y-weight 3.
- `[3,3,3,1,1,1,1,5,5,1,1,1]` parses as X-weight 9, Y-weight 4, X-weight 10, trailing Y-weight 3.
- `[3,3,3,5,3,5,3,1,1,1,1,1]` parses as X-weight 25, trailing Y-weight 5.

This resembles the `Core` / `StackGood` / `unwindGap` architecture in [`Raw391LEBlockRuns.md`](Raw391LEBlockRuns.md), but it is not yet the same formal language or a verified transport of that proof. The working hypothesis is that the A/F sweeps save X-run weights as stack frames and later unwind them across Y-runs. The left-tape traces are suggestive, not a proof of that interpretation.

## Search already attempted

- The bounded FAR/SMT search for 5777 found no certificate at DFA sizes 1–7 in the completed orientations; both size-8 orientations timed out.
- For residual 180, sizes 1–6 found no certificate; at size 7 one orientation was UNSAT and the other timed out; both size-8 orientations timed out.
- A radius-0-through-8 local-window closure is too coarse: arbitrary unseen far bits introduce spurious halt contexts.

These are bounded negative search results only. They do not establish that a regular invariant does not exist, and they do not classify any residual.

## Highest-value next steps

1. Run `python3 im-results/agent11-raw39/gaplist_orbit.py --iterations 20` (or the corresponding CI target) to reproduce the boundary data independently.
2. Formalize the candidate `GapCore` language and a saved-run stack encoding. Determine whether the actual tape view should use a trailing-Y suffix, a reflected view, or a different phase boundary.
3. Derive the exact small-step `run0` lemmas for the P and Q phases. The Q theorem must be parameterized over the three F1 actions while proving a common output tail.
4. Prove a recursive scan/unwind theorem for every `GapCore` input in the reachable grammar, including the base cases. Only then can the proof exclude C1 and establish nonhalting.
5. Keep residual 180 separate. It did not visit F1 in a one-million-step blank simulation, but that observation and the bounded FAR search are not a proof.

The source-inspection target `inspect-1LE-proof-sources` in `.github/workflows/agent11-raw39-more.yml` extracts the full `Raw391LEBlockRuns` and `Raw391LE12198` proof sources from their packed archives. Use them as proof-pattern references, not as evidence that this new grammar has already been proved.
