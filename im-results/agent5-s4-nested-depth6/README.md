# S4 nested suffix renormalization through six levels

**Status:** intermediate computational result; not a proof of S4 nonhalting and not a BB(6) result.

This extends the existing S4 18-digit prefix / 386-gate reduction, the 10-digit / 4,603-gate reduction, and the 7-digit / 28,802-gate reduction. It adds three further exact suffix maps and verifies their mass identities.

Run the self-contained reproduction with:

```sh
node s4_nested_depth6.mjs
```

The script is deterministic and uses no third-party packages. The first 18-prefix scan uses JavaScript `Number` only while the entire prefix mass is bounded below (2^{53}); it asserts that bound at each 327,680-return block. Every later prefix transition, full-stack gate, offset, and sum uses `BigInt`.

## Six-level hierarchy

Each row records the effective gate word (C=(c_0,ldots,c_{g-1})) obtained after the stated prefix cycle. The identity

[
sum_i c_i + 2g = 1024N
]

is checked exactly, where (N) is the number of reduced (P)-returns represented by that word.

| Word | Prefix cycle used | Blocks of previous word | Effective gates | Head additions | Offset sum | Reduced returns (N) |
|---|---:|---:|---:|---:|---:|---:|
| (Q) | 18 digits | 64 blocks of 327,680 (P)-returns | 386 | 402 | 21,474,835,708 | 20,971,520 |
| (R) | 10 digits | 12,800 (Q)-blocks | 4,603 | 4,597 | 274,877,906,934,794 | 268,435,456,000 |
| (V) | 7 digits | 800 (R)-blocks | 28,802 | 28,830 | 219,902,325,555,142,396 | 214,748,364,800,000 |
| (W) | 8 digits | 64 (V)-blocks | 7,278 | 7,149 | 14,073,748,835,532,785,444 | 13,743,895,347,200,000 |
| (X) | 7 digits | 640 (W)-blocks | 36,457 | 36,489 | 9,007,199,254,740,991,927,086 | 8,796,093,022,208,000,000 |
| (Y) | 8 digits | 128 (X)-blocks | 18,084 | 18,096 | 1,152,921,504,606,846,975,963,832 | 1,125,899,906,842,624,000,000 |

The first three rows reproduce the previously recorded reductions. The new rows are (W,X,Y).

## New prefix cycles

The exact-integer reproduction finds:

- Under (V), the first eight digits of the suffix after 35 digits have preperiod 1 and period 64.
- Under (W), the first seven digits of the suffix after 43 digits have preperiod 1 and period 640.
- Under (X), the first eight digits of the suffix after 50 digits have preperiod 1 and period 128.

The (Y) word is extracted from the resulting 8-digit (X)-cycle. The next prefix cycle under (Y) has not yet been determined.

The script also applies (Q^{107}), (R), (V), (W), (X), and (Y) to the corresponding modeled full suffixes. Every full-stack (G)-application in those finite segments succeeds; the resulting states are emitted by the script.

## Evidence boundary

The starting 18-digit prefix and `blockRootTail` are the numerical state used by the existing C++ S4 suffix macro at its first-level macro boundary. The prefix-period scans and this extension are computational, not Lean-kernel checked. In particular:

1. The bridge from the source-certified return-5457 state to this macro-boundary full stack is not established here as a Lean theorem.
2. The 18-prefix period and the later nested cycles still need kernel-checked certificates.
3. The six-level reduction does not establish that every future gate fails, nor that the S4 machine is nonhalting.
4. Consequently, it does not improve the proven BB(6) upper bound or determine BB(6).

The mass identities are exact arithmetic checks on the extracted words; they are consistency checks, not substitutes for the missing source and all-time proofs.

## Useful existing context

- `../agent5-s4-prefix-causal/s4_suffix_macro.cpp`: first-level 18-prefix macro.
- `../agent5-s4-prefix-causal/s4_nested_macro.cpp`: second-level 10-prefix macro.
- `../agent5-s4-prefix-causal/s4_third_macro.cpp`: third-level 7-prefix macro.
- `../agent5-s4-prefix-causal/TENTH-ATTRACTOR.md`: earlier 10th-coordinate contraction analysis.
- `../agent5-s4-prefix-causal/README.md`: earlier source and prefix-causality context.

## Highest-value next work

1. Execute this script under Node in CI and retain the machine-readable output.
2. Prove the 18-prefix cycle and the (Q)-word extraction in Lean, then prove the modeled full-stack bridge from the source-certified root.
3. Find the next prefix cycle under (Y) and extract the seventh-level word.
4. More importantly, seek a uniform all-time obstruction to (W(S)+c) being a power of two, or an actual halting witness. Merely adding deeper finite prefixes is not itself a solution.


## Execution status

The transition logic and numerical outputs were exercised interactively in the V8 runtime during this research session. The committed `.mjs` consolidates that computation into one deterministic Node program, but the file itself has not yet been executed by repository CI. Treat it as a reproducibility artifact pending that run, not as CI-certified output.
