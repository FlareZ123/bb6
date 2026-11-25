# Recursive high-counter grammar for the F1=0LE residual

**Status:** kernel-checked recursive encoding and finite trace fit; not yet a proof of nonhalting.

## Boundary representation

Agent 19's counter trace records configurations in state C with current symbol 0, left side `1`, and right side decomposed as

`00 · (110000)^n · 001111 · L[n mod 6] · H[⌊n/3⌋]`,

at the representative subsequence `n = 3k + 1`. Thus the high counter is `H[k]`; the low code alternates between the residue-1 and residue-4 words along this subsequence.

The observed high blocks are 5-bit words, represented below by their integer values 0..31.

## Exact recursive grammar inferred from k=0..37

Seeds:

- `H(0) = []`
- `H(1) = [31]`
- `H(2) = [1,31]`
- `H(3) = [28,1,31]`
- `H(4) = [7,29,31]`
- `H(5) = [31,29,31]`

For `k ≥ 6`, write `k = 6m+r`, with `m ≥ 1` and `0 ≤ r < 6`. Then

`H(6m+r) = A[r, m mod 2] ++ H(m)`.

Odd-`m` prefixes:

| r | A[r, odd] |
|---:|---|
| 0 | [0,6,1] |
| 1 | [31,6,1] |
| 2 | [1,30,1] |
| 3 | [28,3,31] |
| 4 | [7,31,31] |
| 5 | [31,31,31] |

Even-`m` prefixes:

| r | A[r, even] |
|---:|---|
| 0 | [0,0,0] |
| 1 | [31,0,0] |
| 2 | [1,31,0] |
| 3 | [28,1,31] |
| 4 | [7,29,31] |
| 5 | [31,29,31] |

The recursion is a base-six digit grammar. The prefix depends on the current low digit `r` and the parity of the next base-six digit `m mod 6` (equivalently `m mod 2`). For `r<5`, incrementing k changes only the leading three-block prefix. At `r=5`, the carry recursively increments m and therefore updates the suffix H(m).

## Formalization

- `HighCounterGrammar.lean` defines H structurally over little-endian base-six digits.
- It proves the quotient recurrence, the three-block length increment, and the parity formulation.
- `matches_observed` is kernel-checked and confirms exact equality with all 38 observed rows, k=0..37.
- The proof uses no `sorry` or `native_decide`; the finite agreement theorem is closed by kernel reduction.

## What remains open

The finite fit and recursive grammar do **not** establish that the Turing machine reaches this boundary configuration for every k, nor that its execution from the k-th boundary to the (k+1)-st boundary follows the grammar. The decisive next result is a machine-level macro theorem:

1. prove the state-C boundary configuration has the stated form for arbitrary k;
2. prove the machine's sweep implements the six prefix transitions;
3. handle the r=5 carry by recursion on m, using the same H grammar;
4. show every intermediate configuration avoids the undefined F0 query.

The carry case is the central proof obligation. The grammar makes it explicit rather than hiding it in a long empirical trace.

The data were extracted from Agent 19's run 45586978698 (`high-counter.csv` and `counter-trace.csv`). The source-level machine proof remains uncompleted.
