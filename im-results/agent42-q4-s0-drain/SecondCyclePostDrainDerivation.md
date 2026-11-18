# Second-cycle post-drain continuation: coordinate derivation

**Status:** derived from the P2 frame and the TM2 table; not yet a compiled Lean composition.

Use the notation in Agent 48's `PositiveZSecondCyclePrefix.lean`:

- checkpoint-2 head: `h0 = 1`;
- fixed 34-step bridge moves the state-4 head to `h1 = 5`;
- first right one-run length: `m = 3*2^z + 3*z + 7`;
- after the two-zero setup, the state-1 scan starts at `h2 = m+7`;
- its `n = 2^(2^z-1)` three-one blocks end at `g = h2+3*n = m+7+3*n`;
- the 29-step q4 tail outputs state 3 at `H = g-5 = m+2+3*n`.

The q4-tail left-counter lemma gives the output left-facing prefix
`d0pow(n-1)`, of length `3*(n-1)`. Hence the residual left context
starts at absolute cell `H - 3*(n-1) = m+5`.

Its first cells have a direct provenance:

| Residual index | Absolute cell | Source | Bit |
|---:|---:|---|---:|
| 0 | `m+5` | first zero of the two-zero setup, written to one | 1 |
| 1 through `m` | `m+4` down to 5 | the `m`-cell first unary run | 1 |
| `m+1` through `m+7` | 4 down to -2 | seven marked cells of the 34-step frame | 1 |
| `m+8` through `m+11` | -3 down to -6 | four unmarked cells inside the 34-step frame | 0 |

Thus the exact residual prefix expected from the P2 output is

`replicate (m+8) true ++ replicate 4 false ++ tail`.

After the S0 counted drain, the `d0pow(n-1)` prefix becomes
`d1pow(n-1)`. The contiguous left-one run then has length

`K = 3*(n-1) + (m+8) = 3*n+m+5 = H+3`.

A counted left sweep of `K` ones therefore reaches head `-3`.
The four cells `-6,-5,-4,-3` remain zero; the sweep itself makes
cell `-2` the zero sentinel. The four-step state-3 bridge in
SecondCyclePostDrainBridge.lean then enters state 1 at head `-1`.

On the right, the drained S0 suffix at head `H` is

`0 ++ 111 ++ 00 ++ replicate (3*2^(n-1)) true`.

The left sweep writes cells `-1` through `H+1` to one. Together
with the unchanged three ones at `H+2,H+3,H+4`, the state-1 head
at `-1` sees a one-run through `H+4`, of length

`R = H+6 = m+8+3*n = 3*(n+2^z+z+5)`.

The state-1 three-one-block scan therefore ends at head `H+5`.
Its last output block is `001`, while cells `H+5,H+6` are the
two zeros and cell `H+7` is the first one of the remaining large
right unary counter. This is exactly the six-cell input of the
eight-step bridge in SecondCyclePostDrainBridge.lean. That bridge
enters state 4 at `H+7`.

The state-4 run remaining to scan is `3*2^(n-1)` ones. The finite
prefix cost before this E-scan is

`3*K + 4 + R + 8 = 12*n + 12*2^z + 12*z + 63`.

The E-scan adds `3*2^(n-1)` steps.

## Exact remaining proof obligations

1. Prove the residual-left table directly from the frame output of
   `secondCyclePrefix_from_checkpoint`, using the q4-tail left-counter
   lemma for the `d0pow(n-1)` prefix.
2. Prove that the S0 drain preserves this residual context and changes
   the left counter to `d1pow(n-1)`, while the right suffix becomes
   `s0RightFacing(2^(n-1)-1)`.
3. Compose the counted left sweep, the 4-step zero bridge, the
   state-1 block scan, the 8-step bridge, and the state-4 E-scan.
4. Compile the ordered import closure and check the axiom reports.

No claim about a completed second-cycle q4 checkpoint or BB(6) upper
bound is made here.
