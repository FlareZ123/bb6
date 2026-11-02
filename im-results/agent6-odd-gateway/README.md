# Agent 6: blank-reachable odd-sector gateway restriction

**Status:** Intermediate formal research, not a BB(6) decision or a global-bound improvement. All results concern an independently transcribed accelerated counter map, with the original machine-to-map proof supplied separately by DeepMind's `BusyBeaver/BB6/M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE.lean`. Keep here under `im-results/`.

Target: `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`, actual published blank-entry counter state `(2,1)`.

## Kernel-checked results

Files, in import order:

1. `OddGatewayMod8.lean` defines the recursive drain `G` and odd-sector return `U`, and proves `U_four_multiple_right_three`: for every `a % 4 = 0` and odd `c >= 5`, if `(U a c).2 = 3`, then `(U a c).1 % 8 = 4`. It also proves the nested-drain modular subcases. This assertion is for **all** synthetic inputs satisfying the antecedent.
2. `ReachableOdd.lean` defines exact `T`, `runT`, proves `G_first_mod4` and `blank_odd_section_restriction`: along every surviving actual blank-entry trace, an odd right coordinate paired with even left coordinate has left coordinate 2 or divisible by 4. The special synthetic left coordinate 2 has `(U 2 c).2 = 3` exactly when `c = 15`.
3. `MassRestriction.lean` reproves the published strict sum-of-counters growth (previously also checked by Agent 1), certificates the actual initial 15 states, and proves `blank_ne_two_fifteen`: **the actual blank-entry orbit never visits (2,15) at any finite time**. Indeed any visit at time n would require `3+n <= 17`, hence `n < 15`; all these exact finite indices are separately checked in Lean.
4. `GatewayBlank.lean` combines them in `blank_U_three_left_mod8`: for any blank-reachable hub `(a,c)` with even `a`, odd `c >= 5`, and `(U a c).2 = 3`, we must have `(U a c).1 % 8 = 4`. Its corollary `blank_U_three_next_reset_mod8` shows that its subsequent zero-reset coordinate `(U a c).1+5` equals 1 modulo 8.

All the files compile under Lean 4.36.0-rc2. The main `#print axioms` reports standard `propext`, `Classical.choice` and `Quot.sound`, with no `sorryAx`. The numerical trace is checked as exact equalities by Lean, while the mass growth proof is quantified over arbitrary natural counters.

## Reproduce

Obtain the installed Lean 4.36.0-rc2 executable, then compile the four files in order with `lean -o OddGatewayMod8.olean OddGatewayMod8.lean`, `lean -o ReachableOdd.olean ReachableOdd.lean`, `lean -o MassRestriction.olean MassRestriction.lean`, and `lean GatewayBlank.lean`, with the local directory in `LEAN_PATH`. There is no Mathlib dependency.

## Precise limitation and next proof obligation

A reachable odd-sector gateway into `c = 3` has now been restricted to left residue 4 modulo 8, but this does **not** classify every odd zero-reset. In particular, positive even-counter excursions can independently reach `c = 2` and produce odd zero-resets, and they can exit via the recursive drain into an odd `c=3` hub. The blanket conjecture that every odd reset is 1 modulo 8 remains unproved. Arbitrary synthetic inputs can violate it. A useful next target is to classify exactly which even-excursion exit routes are reachable from `(2,1)`, or to rule out the critical return values `14*2^n - 2*n - 11` established by Agents 1/4/5.

This result advances a **conditional reachable-set property** of the genuine blank orbit; it does not decide halting, and does not establish any new value or upper bound for BB(6).

## Further verified finite exclusions

`FiniteTarget42.lean`, `Trace96.lean`, and `FiniteTarget96.lean` establish, with Lean 4.36.0-rc2 and no `sorryAx`, that the actual blank-entry orbit never reaches the critical states `(2,42)` or `(2,96)`. These are the n=2 and n=3 members of the halting-critical family. Agent 4 independently excluded the earlier `(2,4)` and `(2,16)` states. The reusable theorem `blank_unreachable_after_mass_cutoff` combines strict counter-mass growth with explicit checked prefixes. Every fixed bounded-mass target can be decided this way by finite computation; the infinitely growing target family remains unresolved. Compile the three added files in the stated order, retaining each `.olean` and its directory in `LEAN_PATH`.
