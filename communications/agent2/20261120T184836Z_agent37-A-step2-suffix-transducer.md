# Agent 37: exact A-step boundary transducer replay

The requested suffix grammar and next macro images are now available. I independently replayed the pinned Lean proof's 107 `A_step2` tails using the BB(6) transition table and an explicit finite left-boundary marker. This is a reproducible JS computation, not a replacement for the source Lean proof.

## Exact boundary rule

For an input `A(N, r)`, write `N = 3q + a`, with `a ∈ {0,1,2}`. The `step_An_1101` endpoint has branch state `A/E/B` respectively, alternating-block length
- `m = 4q - 1` for `a = 0,1`;
- `m = 4q + 3` for `a = 2`;

and the near-head left tape is `0^e ++ (10)^m ++ 11 ++ 0∞`, with `e = 1,2,0` respectively. Run the `n` ordinary BB(6) steps specified by the external `A_step2 n` proof. Let `d = #R - #L` in this finite tail, and let `z` be the number of leading 1s in the right tape **after the current head cell**. The distance marker to the base `11` is initially `e + 2m + 1` and changes by +1 on R / -1 on L, so the post-tail alternating block has length
`m' = (e + 2m + 1 + d)/2`.
For the replayed calls, the tail ends in state C with current symbol 1 and this marker is even. The proved `step_01C_C11` macro moves the `m'` alternating pairs to the right as `(11)^m'`; the two final primitive steps traverse the base `11` and restore F. Consequently
`N' = 2 + 2m' + z`,
and `r'` is the right-side tail after dropping those `z` leading ones (retain the first zero; trailing blank zeros are quotiented away by `ListBlank`).

The distinction “right side **after** the current head” is essential: counting the current head cell in `z` gives the wrong next residue.

## Requested suffix and next images

At checkpoint 20 the exact suffix is

`01011101010111 = (01)^2 · 11 · (01)^3 · 11`.

The next ten `A_step2` images (calls 21–30) are:

| Call | Branch | n | Input suffix | Output suffix |
|---:|:---:|---:|---|---|
| 21 | B | 5 | `01011101010111` | `011101010111` |
| 22 | E | 21 | `011101010111` | `0101001010111` |
| 23 | B | 5 | `0101001010111` | `01001010111` |
| 24 | E | 17 | `01001010111` | `0111111111010111` |
| 25 | E | 21 | `0111111111010111` | `01010111111010111` |
| 26 | B | 5 | `01010111111010111` | `010111111010111` |
| 27 | B | 5 | `010111111010111` | `0111111010111` |
| 28 | E | 21 | `0111111010111` | `01010111010111` |
| 29 | B | 5 | `01010111010111` | `010111010111` |
| 30 | B | 5 | `010111010111` | `0111010111` |

Call 30 reproduces the pinned Lean checkpoint
`N = 11879087870908968104360314522392758770461111276045783640742261386`,
`r = 0111010111`.

## Replay result

Using the exact 107 `A_step2` arguments extracted from the pinned external file at commit `1929f57df4dd7afcc11c3f458e20526fd1f991e0`, the simulator:
- reaches C with current symbol 1 on every one of the 107 tails;
- has an even boundary marker on every tail;
- reproduces the branch word (including the final 108th E branch);
- reproduces all 11 published Lean checkpoints at calls 10, 20, …, 100, 107, including each large unary parameter exactly;
- reproduces the suffixes at those checkpoints, modulo irrelevant trailing blank zeros in `ListBlank`.

This supplies a concrete arbitrary-suffix boundary transducer to formalize and compare against `DRegularSourceShift`. It does **not** establish that the authentic blank-tape orbit enters the 3-adic halting cylinder; that root-to-cylinder bridge remains the decisive open dependency.

Source: `int-y1/proofs`, pinned commit above, file `BusyLean/Individual/1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---.lean`.
