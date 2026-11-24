# Four-root suffix/phase diagnostics (intermediate)

This directory preserves targeted diagnostics for the D-family section-return map. It is **not** a BB(6) result, a Lean proof, or an all-time nonhalting argument. Keep it in `im-results/`.

## Inputs and reproduction

- `../agent36-cryptid-trace/trace_four_starts.py`: the existing 30,000-step projected section grammar and the four authentic root seeds.
- `../agent32-d-route-dag/route_bfs.py`: the finite E-front interpreter.
- `metrics.py`: wrapper that imports those existing implementations, recomputes suffix/phase statistics, and checks the synthetic E-front regression case. Run from the repository root with `python3 im-results/agent2-d-section-phase-diagnostics/metrics.py`.

The 30k figures below were first obtained by a direct JavaScript reimplementation of the same `trace_four_starts.py` recurrence. The Python wrapper is committed to make the diagnostics independently reproducible; its execution was not available in this invocation.

## Four-root projected trace statistics

The four input roots are the source-certified sections D0-A/I9, D3-B/I5, D2-C/I15, D1-F/I39. Each trace uses 30,000 applications of the existing projected macro recurrence (120,000 total).

| Root | Distinct suffixes | Distinct (suffix, n mod 3) | Distinct (suffix, n mod 9) | Max suffix length | Max rank R |
|---|---:|---:|---:|---:|---:|
| D0-A | 64 | 154 | 332 | 26 | 30 |
| D3-B | 75 | 175 | 356 | 25 | 29 |
| D2-C | 65 | 158 | 333 | 26 | 30 |
| D1-F | 63 | 136 | 288 | 26 | 30 |

Across all four traces:

- 90 distinct suffixes occur.
- 218 distinct `(suffix, n mod 3)` pairs and 511 distinct `(suffix, n mod 9)` pairs occur.
- The maximum observed per-macro rank increase is 9.
- No observed output has `R(suffix) > n`.
- No exact `(n, suffix)` state is shared between two of the four traces during this finite window.
- The final unary-counter bit lengths are 42,455; 42,454; 42,456; and 42,457, matching the values recorded in Agent36's full research log.

Here
[
R(w)=|\operatorname{trim}(w)|+2\,\operatorname{occ}_{011}(\operatorname{trim}(w)),
]
where `trim` removes trailing zeroes. Since occurrences of `011` cannot overlap, (R(w)\leq 5|\operatorname{trim}(w)|/3).

The 511 mod-9 phase keys are **not** a deterministic quotient: 355 keys have multiple observed next-phase outputs when the same `(suffix, n mod 9)` is revisited. The analogous ambiguity counts for moduli 3, 9, 27, 81, 243, 729 are 165/218, 355/511, 654/1106, 1252/2192, 2541/4349, 4723/8653. A fixed low residue cannot replace the missing quotient/carry phase; this is consistent with the affine (3^L\to8^L) digit shift.

## Synthetic E-front regression case

A suffix-only overapproximation that freely chooses A/E/B residues can reach the following 14th E branch from the section ((n,suffix)=(1,823,245,\epsilon)):

- 13 preceding projected branches: `EEEBBBEEEBEEE`;
- resulting section: (n=628,692,084,481), suffix `010101010110111111`, next residue E;
- the short E parser in `trace_four_starts.py` has no listed gate for the residual `1101\ldots` pattern.

The full finite E-front interpreter `route_bfs.efront(suffix, 12)` instead reports a return after 46 primitive steps, with left-pair count 10 and raw output suffix `01111111111111101010111`. Its affine output constant is 5, giving (n'=1,676,512,225,277). The input suffix has (R=22), the output suffix has (R=27), so the observed rank increment is 5.

This is a **synthetic section test**, not one of the four blank-root trajectories. It is a finite interpreter result, not a kernel-checked path certificate. It shows that the short macro list is not exhaustive over arbitrary suffixes; the general E-front interface is needed, or a root-specific phase invariant must prove this class unreachable.

## Research implication

The actual four-root traces visit a small suffix alphabet over the measured horizon, but suffix alone and any fixed low ternary residue are insufficient as an all-time state. A useful carrier must include the appropriate quotient/carry phase (or a source-proved root-specific prefix language), include all four seeds, and close every A/B/E transition including exceptional E-front cases. Do not promote the 30k statistics to an invariant or repeat the horizon scan without a new discriminating hypothesis.
