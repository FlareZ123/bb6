# Agent 45 — bounded D four-root replay

**Question.** Do the three non-`I_9` authentic D seeds enter the prepared 108-layer E/B halting-route DAG quickly, or does the existing I9-only route remain the strongest candidate?

**Method.** Reused Agent 32's existing `im-results/agent32-d-route-dag/route-block-cpp.tar.xz.b64` bundle unchanged. Extracted `dblock.cpp`, `dag.tsv`, and the independent `ddirect.py` / `dsuffix.py` implementation. Compiled with `g++ -O3 -std=c++17 dblock.cpp -lgmpxx -lgmp -o dblock`. Ran the exact block evaluator for 1,000,000 return transitions from each authentic pure-section seed `I_5`, `I_15`, and `I_39`, with empty suffix. The evaluator uses the same A/E/B section transitions and DAG-prefix matcher as the existing I9 replay.

The DAG matcher tracks the longest consecutive suffix/branch path matching a prefix of the prepared 108-layer halting DAG; a full 108-edge match would reach its certified terminal. A/E/B branch counts below are in that order.

## Exact block replay

| Seed | Returns | Halt/unresolved status | Final unary parameter bits | Final suffix | Pure returns | Best DAG prefix | At return | A / E / B |
|---|---:|---:|---:|---|---:|---:|---:|---:|
| I5 | 1,000,000 | none (status 0) | 1,415,041 | `01010111` | 609,833 | 17 / 108 | 952,852 | 333,610 / 333,386 / 333,004 |
| I15 | 1,000,000 | none (status 0) | 1,415,042 | `01010111` | 609,260 | 15 / 108 | 541,276 | 332,202 / 334,239 / 333,559 |
| I39 | 1,000,000 | none (status 0) | 1,415,043 | empty | 611,257 | 15 / 108 | 760,756 | 334,688 / 332,744 / 332,568 |

The final unary-parameter SHA-256 hashes (hex representation, without newline) are:

- I5: `492fd5b9f5d326562a42620cd6be8c467a4eddcc53f68794b8a6febc7cc4b03e`
- I15: `9bd9349e3021d8fdddf53979360354970aab36240f0d70751116673e04787722`
- I39: `b18c107ae37f677a5d9d6a8a34d7abff9a5abc008087331182b71f70db7451c1`

## Independent endpoint check

Ran the direct Python `ddirect.step` implementation for 100,000 returns from each seed. It agreed exactly with the C++ block evaluator on both the final arbitrary-precision integer and suffix:

| Seed | Final bits | Final suffix | SHA-256 of final integer in hex |
|---|---:|---|---|
| I5 | 141,507 | empty | `d0b5beb6ae3cbe9ddd793eb3fa74177dac74cca4a60daaa68451c8fa0b098d05` |
| I15 | 141,508 | empty | `ace530ee033e3ffb68d3a97adbe1b565ac9e0ad17e61e83915540cc33a894c7e` |
| I39 | 141,510 | `0111111` | `88b0788dc6e4728451640060515303b3fc675c00eb399c22aa7c0ec9d8d78e84` |

A separate raw-tape simulation of the six-state D0 table for 1,000,000 primitive steps found no halt and observed the following exact pure-section returns:

- I5: step 101 → I17; step 686 → I49; step 26,392 → I343.
- I15: step 432 → I43.
- I39: step 2,360 → I107; step 18,815 → I289; step 930,852 → I2059.

These raw returns are an early-transition cross-check, not a proof of the full macro replay.

## Interpretation and next action

Within the tested million-return window, none of I5/I15/I39 halted or reached a long prefix of the prepared halting DAG. Their best matches (15–17 layers) are materially shorter than the previously reported I9 best match (27 layers in the existing I9 run). This supports prioritizing I9 for further route-membership work and not spending another billion-return run on I5/I15/I39 without a new discriminating hypothesis.

**Scope limitation.** This is exact bounded computational evidence only. It does not prove any of the four roots nonhalting, and the 108-layer route is only one prepared halting family. It does not rule out other halting routes or later entry into this DAG.

## Reproduction

From the extracted bundle directory:

```sh
g++ -O3 -std=c++17 dblock.cpp -lgmpxx -lgmp -o dblock
./dblock 1000000 /tmp/i5.end dag.tsv 5 ""
./dblock 1000000 /tmp/i15.end dag.tsv 15 ""
./dblock 1000000 /tmp/i39.end dag.tsv 39 ""
```

For an independent 100,000-return endpoint check, use `ddirect.py` with `dsuffix.py` and seed values 5, 15, and 39. The direct implementation is slower but agreed exactly on all three endpoints.
