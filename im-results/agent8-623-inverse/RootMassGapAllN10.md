# Candidate complete exclusion of the n=10 terminal-cancellation corridors

**Status: proof plan with unverified checkpoint values.** The ratio/mass arithmetic is exact, but the additional root states below currently come from a JavaScript replay of the source transcription. Do not call this a Lean-proved result until the states are checked by `decide` against `Agent49ParitySource` and the consumer is compiled with an axiom audit.

## Two ratio geometries from the cancellation bridge

For a predecessor state with smaller coordinate (m), the n=10 ternary band is
`19680 = 3^9-3 <= m <= 3^10-4 = 59045`.

The four terminal-window / previous-ray combinations reduce to two predecessor geometries:

- Far previous ray: `|L-13m| <= E`.
- Near previous ray: `|4L-7m| <= E`.

The current bridge uses `E <= 35*n+120 = 470` at n=10. Here (L) is the larger coordinate.

## Near 7:4 corridor

From `|4L-7m|<=470`,
`11m-470 <= 4(L+m) <= 11m+470`.
For `19680 <= m <= 59045`, integer total mass therefore satisfies
`54003 <= L+m <= 162491`.

The source-transcribed root masses at steps 33 and 38 are:
- step 33: D(19954,27733), mass 47687;
- step 38: D(44634,124427), mass 169061.

Thus a root state in the near corridor must be one of steps 34–37. The source-transcribed intermediate states and exact 7:4 residuals are:

| step | state | `|4L-7m|` |
|---:|---|---:|
| 34 | D(7784,59872) | 185000 |
| 35 | D(52084,23375) | 44711 |
| 36 | D(28698,70161) | 79758 |
| 37 | D(41468,86104) | 54140 |

Every residual exceeds 470.

## Far 13:1 corridor

From `|L-13m|<=470`,
`14m-470 <= L+m <= 14m+470`.
For `19680 <= m <= 59045`, total mass lies in
`275050 <= L+m <= 827100`.

The source-transcribed root masses at steps 39 and 46 are:
- step 39: D(79788,133932), mass 213720;
- step 46: D(426044,571540), mass 997584.

Thus a root state in the far corridor must be one of steps 40–45. The source-transcribed intermediate states and exact 13:1 residuals are:

| step | state | `|L-13m|` |
|---:|---|---:|
| 40 | D(54138,239399) | 464395 |
| 41 | D(185262,162438) | 1926432 |
| 42 | D(22822,487342) | 190656 |
| 43 | D(464518,68489) | 425839 |
| 44 | D(396018,205505) | 2275547 |
| 45 | D(190506,616551) | 1860027 |

Every residual exceeds 470.

## Formal proof structure

1. Prove the listed root checkpoints by `decide` against the actual `Agent49ParitySource.run`.
2. Use `run_mass_mono` / `next_strict_mass` to show a root visit whose mass lies strictly between the endpoint checkpoint masses must occur at one of the intervening indices.
3. Split those finitely many indices and use the exact checkpoint states to contradict the corresponding ratio residual bound.
4. Instantiate the far and near corridor bounds from the four theorems in `RootCancellationBudgetBridge.lean`.

If the checkpoint list and source bridge inequalities are confirmed, this proves that all four n=10 cancellation sectors are absent from the genuine blank-root orbit. It would resolve the entire n=10 terminal-budget layer, but it would not by itself resolve n>=11 or prove #623 nonhalting.

Keep this in `im-results/`; no claim belongs in `results/` until the source proof is complete.
