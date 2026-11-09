# #623: exact ternary digit-charge cocycle and authentic return equations

**Research status, 9 November 2026.** This is an exact all-input mathematical reduction of the original Cryptids #623 complete B-drain. The formulas below have been checked in a standalone Lean 4.36.0-rc2 faithful model, with only standard logical axioms. The final unmodified-original-source import verification is recorded in the linked GitHub Actions workflow when complete. This is an **intermediate**, original-root-relevant tool. It does not prove that the genuine blank-start machine halts or never halts, and does not determine BB(6).

## Exact reduction

The original source machine is `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA`, with accelerator `D(a,d)` and authentic blank root `D(0,7)`. Agent49's [original-source complete flattening](../agent49-parity623/FlatDrain.md) proves that its complete `drainB(a,b,d)` agrees with a one-level ternary interpreter. The source-immediate recursion is used here, without a new interpretation of the physical machine.

Define a partial two-input function `digitCode(a,b) = some(A,C)` to mean that the complete B-drain succeeds, produces final first counter `A`, and accumulates digit charge `C`. Its exact computation is:

| Input | Recursive child | Added digit charge |
| --- | --- | ---: |
| `b=0` | terminal `(a,0)` | 0 |
| `b=3q>0` | `(a+1,q-1)` | 0 |
| `b=3q+1, a>0` | `(a-1,q)` | 4 |
| `b=3q+1, a=0` | failure | — |
| `b=3q+2, a>0` | `(a-1,q+1)` | 2 |
| `b=3q+2, a=0` | `(0,q)` | 1 |

Charges add on successful return from the child. All recursive block counts decrease strictly. The all-natural, original-source-level assertion is

```text
drainB(a,b,d) = none       iff digitCode(a,b) = none
drainB(a,b,d) = some D(A,D)
                  iff digitCode(a,b) = some (A,C)
                      and D = d + 3*b + C
```

where the second statement existentially quantifies the unique `C`. It is **an exact equality of the output**, stronger information than a success indicator or a uniform O(log b) counter bound. The source theorem is [`drainB_digitCode`](DrainDigitChargeSource.lean), derived directly from the preexisting [`flatB_eq_drainB`](../agent49-parity623/FlatDrainSource.lean).

## Exact joint-mass cocycle

Define `excessMass(a,b)` on the **same** partial domain, with a charge of **1** for each successful positive-block reduction, except a positive-first-counter `b≡1 (mod 3)` reduction costs **3**. In the other three nonterminal branches the cost is 1. Then

```text
digitCode(a,b) = some (A,C)
    => excessMass(a,b) = some E
       and A + C = a + E.
```

In particular, for the original, source-connected complete drain,

```text
drainB(a,b,d) = some D(A,D)
    => there is a unique E such that
       excessMass(a,b) = some E
       and A + D = a + d + 3*b + E.
```

Equivalently, `E = N + 2*N₁`, where `N` is the number of positive-block ternary reductions and `N₁` counts the positive-first-counter residue-one reductions. This identity telescopes exact one-digit changes of the pair `(A,C)`. It is not a probabilistic approximation or a finite-threshold result.

The original-source theorem file [`DrainMassCocycleSource.lean`](DrainMassCocycleSource.lean) implements the counted recurrence and the dependent output proof; local Lean axiom audit for the same arithmetic proof produced `[propext, Quot.sound]`. These exact charges can be extracted for any true blank-root return without using finite trace sampling.

## Four true-source return branches

For any *successful* original `highLevelNext(D(a,d)) = D(A,D)`, the four branches below have exact output and exact mass formulas, with `C` the above digit charge and `E` the exact mass excess for the listed `(x,b)`:

| Branch conditions | B-drain inputs `(x,b)` | Exact second output | Exact total output mass |
| --- | --- | --- | --- |
| `a>0, d odd, a≥d+5` | `(a-d-5,d+3)` | `D=3d+14+C` | `A+D=a+2d+9+E` |
| `a>0, d even, a≥d+3` | `(a-d-2,d+2)` | `D=3d+8+C` | `A+D=a+2d+6+E` |
| `a>0 even, d odd, a≤d` | `(d+4-a,a-1)` | `D=3a+C` | `A+D=d+2a+4+E` |
| `a=d+2, a,d even` | `(0,a)` | `D=3a+2+C` | `A+D=3a+2+E` |

All formulas follow by an exact split of the unchanged `highLevelNext` source definition, then the digit-charge/mass theorems, with no use of guessed tape states. The Lean statements and their local proofs are in [`RootDigitChargeSource.lean`](RootDigitChargeSource.lean). They are genuinely applicable to each authentic blank-root return satisfying the branch hypotheses. They are still **conditional on success** and do not establish that a particular branch is reached at an arbitrarily late time.

## Verification and next decisive direction

- The stand-alone Lean 4.36.0-rc2 copies of the original arithmetic, including the exact charge code, mass composition, and all eight return-branch statements, compiled without `sorry`; theorem-level audits list only `propext` and `Quot.sound`.
- The existing [manual source-pinned CI workflow](../../.github/workflows/agent49-623-flat-drain.yml) imports the unmodified `google-deepmind/cryptids@c86f15861709b76042998c5211c7b2f83991621b` and compiles the original flattened interpreter and these three source-connected modules. Do not regard a locally tested copy as equivalent to a successful original-source import until that run succeeds.
- The earlier CI attempt [42559828115](https://github.com/FlareZ123/bb6/actions/runs/42559828115) exposed a stale redundant tactic in Agent49's later source module, corrected in [da17d395](https://github.com/FlareZ123/bb6/commit/da17d3951f52014dc53e590c5ce6c13b2755ee22). The following attempt [42561197444](https://github.com/FlareZ123/bb6/actions/runs/42561197444) reached the digit source but found a Lean constructor-equality elaboration mismatch, corrected by direct constructor elimination in [b9f162b5](https://github.com/FlareZ123/bb6/commit/b9f162b506274bde24dcddb724669b2d27f5525d).
- The decisive open obligation is still a **uniform blank-root orbit invariant** separating every actual `D(0,7)` iterate from the known synthetic fatal B-drain cylinders. The exact `E` and `C` values offer a lossless arithmetic trace for root-sensitive inverse congruences; proving such a separation requires more than these formulas.

**Publication qualification:** The reductions are mathematically exact and reproducible, but external novelty against the strongest prior ternary-transducer and existing #623 results is not established. Keep in `im-results/`, not `results/`.
