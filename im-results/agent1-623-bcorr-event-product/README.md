# Source-faithful B-corr S-window event product

## Status

This is an intermediate computational result, not a publishable proof and not a determination of BB(6). It supersedes the retracted conservative-window diagnostic in `im-results/agent1-623-swindow-obstruction-product/`.

The scan uses the exact S-indexed correction-only buffer
\[
B_{\mathrm{corr}}=34\ell_S+122
\]
and the complete source-to-target phase update from `im-results/agent48-623-tight-window/s_window_boundary_phases.js`, including the one- or two-digit low-boundary advance, both sectors/branches, and the coupled 0/1 shifts.

## Finite-trace findings

Range: (D_{33}\to D_{34}) through (D_{10000}\to D_{10001}), 9,968 transitions.

| Quantity | Count |
|---|---:|
| Source-to-target phase keys | 1,318 |
| Observed 211-state universal-subset states | 114 |
| Nonsynchronizing suffixes (subset size > 1) | 84 |
| Reset failures | 0 |
| Branch/sign-vs-threshold mismatches | 0 |
| Reset-output / reset-recognizer end mismatches | 0 |
| Buffer-relative event / reset end mismatches | 0 |
| Missing exact reset seeds | 0 |
| Exact final carries outside their 211-subsets | 0 |

The 84 nonsynchronizing suffixes agree with the existing `SWindowPostResetSynchronization.md` analysis. They do **not** mean the authentic root carry is unknown: the 736-state reset-output DFA identifies the exact reset seed, and the 66-state closure propagates that seed through the remaining suffix. The 211-state subset remains a universal rank-one diagnostic over all 66 possible seeds.

## Compact event-state product

The 580-state `pair_carry_and_length` buffer-relative DFA is read on each target S-window. At its first output transition, record:

- (i): zero-based event position;
- (q): DFA state immediately before the output transition;
- (s): current input symbol causing the transition;
- (b): second witness symbol, recovered from the rolling five-symbol history as (	ext{history}[6-L]), where (L) is the witness length encoded in the output-label key.

The observed product key is
\[
(\text{source-to-target phase},\ \text{exact final 66-state carry},\ i,q,s,b).
\]

The output state is determined by ((q,s)), so it need not be included. The product has:

- 9,968 distinct keys;
- zero repeated keys;
- zero multi-successor keys;
- 9,967 observed consecutive edges;
- maximum observed outdegree 1.

The exact reset seed is used to calculate the final carry but is not a separate component of this product key. No raw tail-five string or 211-subset state is required in the compact key.

### Ablation

Each row adds the indicated event data to the base ((	ext{phase},	ext{final carry},	ext{buffer output state})) key.

| Buffer descriptor | Distinct keys | Repeated occurrences | Branching keys |
|---|---:|---:|---:|
| Output state only | 9,834 | 134 | 133 |
| Output state + event position | 9,917 | 51 | 51 |
| Output state + pre-output state | 9,953 | 15 | 15 |
| Output state + current symbol | 9,936 | 32 | 32 |
| Output state + second witness symbol | 9,911 | 57 | 57 |
| Output state + pre-state + symbol + second symbol (no position) | 9,966 | 2 | 2 |
| Output state + position + pre-state + symbol + second symbol | 9,968 | 0 | 0 |

The final compact key omits the output state because it is the deterministic transition from the pre-output state under the current symbol.

The 580-state buffer-relative quotient itself has a separate exhaustive finite-word validation in `im-results/agent48-623-tight-window/verify_buffer_relative_postreset.js`: it compares the quotient with the original 736-state output DFA for every word of length at most six and checks recovery of the previous pair and second witness symbol. That verifier checks 597,871 words. This validates the finite automaton quotient, not the all-time root product.

## Reproduction

From the repository root:

```sh
node im-results/agent1-623-bcorr-event-product/analyze_bcorr_event_product.js
```

The script reads the existing root recurrence, reset recognizer, 211-subset DFA, 736-state exact-seed output DFA, 66-state closure, and 580-state buffer-relative quotient. It writes `SourceFaithfulBcorrEventProduct.json` beside itself.

The script has been committed but has not yet been smoke-tested in a local Node shell in this invocation. The counts above were computed in the in-session JavaScript runtime using the same recurrence and automata. Run the script or a focused CI job to reproduce them independently.

## What this does and does not establish

This is a deterministic finite-state encoding of the observed 9,968-step root trajectory. All 9,968 product states are distinct, so it does not yet provide a repeated-state cycle, a closed transition component, or an all-time invariant. It is a compact substrate for deriving the next-state map or a ranking function.

The phase and drain-correction calculations are computational replays of the existing source formulas. The source-linked Lean bridge remains a separate certification obligation: the reported Agent 41 workflow failure occurs before the relevant Agent 1 bridge modules compile. No BB(6) upper bound or exact value is claimed.
