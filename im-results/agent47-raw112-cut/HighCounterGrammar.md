# Recursive high-counter grammar for the F1=0LE residual

**Status:** source-certified all-depth nonhalting proof; the grammar below is its discovery precursor. See [CarryProof.md](CarryProof.md) and CI run [45595822219](https://github.com/FlareZ123/bb6/actions/runs/45595822219).

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

## Machine-level closure

`Raw112HighIncrement.lean` and `Raw112CarrySweeps.lean` prove the recursive carry and outer sweeps at arbitrary depth. `Raw112CarryRoot.lean` joins these into a positive-cost recurrence starting at the blank-entry configuration; `Raw112CarryNever.lean` transfers the result to the original machine semantics. `Raw112SiblingNever.lean` additionally proves the F1=1RB sibling nonhalting via exact bounded stuttering simulation.
