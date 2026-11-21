# Branch-specific source-carry × reset-DFA products

**Status:** exact finite-state composition and reproducible Moore minimization; not an all-time Machine #623 proof.

This implements the previously proposed composition of the branch-specific source-to-target digit transducer with the full `post_reset_pair` DFA. It uses the full 395-state DFA plus two skip states, rather than the 351-state selected interface, so the output is the original full reset label directly.

## Exact construction

The input alphabet is the nine pair symbols
`z = 3*x_digit + y_digit`, with each digit in `{0,1,2}`.

A transducer state is `(prevX, prevY, carryX, carryY)`. For input pair `(x,y)`:

- Left branch:
  - `tx = x - prevY + carryX`
  - `ty = prevY + carryY`
- Right branch:
  - `tx = -x - prevX - prevY + carryX`
  - `ty = prevX + prevY + carryY`

The emitted pair is `(tx mod 3, ty mod 3)`; the next state is
`(x, y, floor(tx/3), floor(ty/3))`.

The complete carry rectangles are used:
- L: 9 previous pairs × 5 × 5 carries = **225** transducer states, with `carryX ∈ [-2,2]`, `carryY ∈ [-2,2]`.
- R: 9 previous pairs × 6 × 5 carries = **270** transducer states, with `carryX ∈ [-4,1]`, `carryY ∈ [-2,2]`.

The reset side is the 395-state `post_reset_pair` machine in `im-results/agent49-parity623/ResetPostStateDFA.json`. Two wrapper states are added:
- offset 1 skips the first emitted pair, then enters the full DFA initial state;
- offset 2 skips the first two emitted pairs, then enters the full DFA initial state.

For each branch, the reachable product is generated from **every** transducer state paired with both offset starts. Each input pair advances the carry transducer; its emitted pair advances the reset DFA. The product's Moore output is the full DFA output label (one of 54 labels, or null before a reset is found).

## Computed product sizes

| Branch | Full Cartesian bound | Reachable product states | Product transitions | Minimal Moore states |
|---|---:|---:|---:|---:|
| L | 89,325 | **3,546** | 31,914 | **1,002** |
| R | 107,190 | **5,538** | 49,842 | **1,307** |

The Moore partition starts with 55 output classes (54 full labels plus null) and stabilizes as follows:

- L: `55, 226, 456, 706, 860, 996, 1002, 1002`
- R: `55, 259, 639, 947, 1120, 1299, 1307, 1307`

The null class must be refined by successor behavior; it is not one congruence class. The stable quotient is the minimal Moore quotient of the reachable product for these 54 full output labels and null.

The committed JSON contains the reachable product states, their quotient-class map, both offset start-class arrays, quotient outputs, quotient transitions, and the refinement counts. The builder checks, for every product state, that its output agrees with its quotient output and that all nine transitions agree with the quotient transition table.

## Reproduction

Run from the repository root:

```bash
node im-results/agent24-machine623-shifted-reset-product/build_source_carry_reset_product.js
node im-results/agent24-machine623-shifted-reset-product/build_source_carry_reset_product.js --verify
node im-results/agent24-machine623-shifted-reset-product/verify_source_carry_reset_product.js
```

The input is `im-results/agent49-parity623/ResetPostStateDFA.json`; the output is `SourceCarryResetProduct.json`.

## What this does—and does not—establish

This is an exact one-window composition: for any finite source digit-pair stream and any initial carry state in the stated rectangle, it computes the full reset-DFA output on the emitted target stream after the selected one- or two-symbol skip. It is much smaller than the naive Cartesian products and provides a reusable, finite transition system for subsequent composition.

It does **not** prove that the authentic blank-root orbit remains in a reset-accepted language. It does not determine the authentic next source word, the next branch, or the next source carry solely from the quotient output. The following obligations remain separate:
1. prove that the authentic `sourceCarry` formulas place each root transition in the full L/R start rectangles;
2. discharge the source drain success and correction-budget hypotheses for every root transition;
3. couple the phase edge, sector, high-bit/drain state, and the next source-to-target transducer;
4. prove the resulting root-specific reachable set is closed (or find a counterexample and refine the invariant).

Keep this as an intermediate result in `im-results/`; it is not yet suitable for `results/`.


## Adversarial regression constraints

The product must remain separate from the known counterexamples; it does not justify unrestricted reset preservation. Keep these cases in every proposed root-closure test:

- `im-results/agent24-machine623-phase-slack-regressions.md`: leading-phase ambiguity, the exact H65 failure `D(18,88) → D(70,65)`, mod-3/mod-9 slack-class failures, and the withdrawn two-sided no-`00` suffix condition.
- `im-results/agent32-623-phase-automaton/ClosureCounterexample.md`: raw reset-language nonclosure and the six eight-symbol whole-window counterexamples covering all three allowed shifts.
- `im-results/agent32-623-phase-automaton/PhaseAutomaton.md`: the index-33 output-suffix counterexample. Closure must be checked on the entire next S-window, including its bounded high-end extension, not on an arbitrary suffix.

In particular, the corrected length-three raw witnesses are L start `(prevX,prevY,cx,cy)=(0,0,-2,-2)), input `00 02 00`, output `11 22 01`; and R start `(0,0,-4,-2)), input `00 01 00`, output `21 12 10`. Both inputs are common reset patterns and both outputs are rejected. These are synthetic full-rectangle witnesses, not authentic-root states.


## Source-derived specialization

The arithmetic start-set restriction and its new three-symbol reset are documented in [SourceDerivedResetPatternDFA.md](SourceDerivedResetPatternDFA.md), with data in [SourceDerivedResetProduct.json](SourceDerivedResetProduct.json). Keep the full-rectangle product and all counterexamples above as the universal baseline; use the source-derived specialization only after the `B<K` source-carry hypotheses are discharged.
