# Agent 50: P1 critical indices n ≡ 10 (mod 16)

**Status:** novel within the shared repository, intermediate all-time reachability exclusion for a published BB(6) counter map. The exact six-state Busy Beaver value remains unknown. The proofs have compiled under Lean 4.36.0-rc2 against *signature-matching local mirrors* of the exact Agent 1 definitions, while imported Agent 1 invariant theorems in the local mirror were represented by axioms. The actual repository `ResetGate.lean` and `PosEvenForm.lean` prove these invariants; full-source integration and axiom audit remain to be performed before claiming a kernel-checked result against the genuine import chain.

Machine: `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`; initial accelerated hub `(2,1)`.

## Main result

`BB6.Agent50P1.blank_no_residual_critical_10_mod16`:

```lean
∀ k : Nat,
  ¬BB6.Agent1.Reach (14*2^(16*k+10)-2*(16*k+10)-16) 3
```

Agent 19's independent `residual_critical_gateway` theorem establishes that, for these critical indices, halting-critical hub reachability is equivalent to reaching this odd-right `c=3` feeder. Consequently, once the Agent 1/Agent 19 reachability representations are formally bridged, this excludes every `n≡10 (mod 16)` critical target from the *real blank-tape orbit*. This is a proper infinite subset of the residual `n≡2 (mod 4)` family. **The remaining residual classes (n mod 16 equal to 2, 6, 14) remain open.**

## Complete proof architecture

Let `n=16k+10` and `s=7*2^(16k+7) - 2k - 3`, hence `s` is odd, `s≥3`, and `H(n)-6=16s+12`. Here `H(n)=14*2^n-2n-10`.

For each positive-output P1 recursive G return to `(16s+12,3)`, `P1Triple.lean` formally exhausts all possible G inputs `(k,v)`:

```text
(4s+2,8s+9), (6s+4,4s+3), (7s+5,2s).
```

A general `positive_G_feeder` lemma maps every reachable G return to its earlier even-left hub `(2k-4,v+4)`, using the already established odd-parent theorem. No candidate has G input v=1 (the exceptional c=3 branch), as each inverse theorem excludes it.

First input forces reachable `(8s,8s+13)`. Its complete G inverses:

```text
(2s-1,12s+13), (5s+2,6s+5), ((13s+7)/2,3s+1).
```

The first two force even-left hubs `(4s-6,12s+17)` and `(10s,6s+9)`, forbidden by the global reachable modular invariant (first counter 2 mod 4 and greater than 2). The last forces `(13s+3,3s+5)`, so Agent 1's even-positive classification would require `13s+15=14*2^j`.

Second input forces reachable `(12s+4,4s+7)`. Its complete G inverses are `(3s,10s+9)` and `((11s+5)/2,5s+3)`. The first is ruled out by the same mod-4 invariant, the second by an exact even-positive classification requiring `11s+13=14*2^j`.

Third input forces reachable `(14s+6,2s+4)`. The power-form classification would require `14s+18=14*2^j`, arithmetically impossible modulo 14.

Finally `P1ResidualArithmetic.lean` proves for all k both `11s+13` and `13s+15` lie strictly between consecutive powers `14*2^(16k+9)` and `14*2^(16k+10)`, so neither can equal `14*2^j`.

No search horizon, finite bound, probabilistic assumption, or `native_decide` is used by this symbolic exclusion.

## Files and reproducibility

- `P1Triple.lean`: all three exact finite G-inverse enumerations, imports the existing `GInverse.lean` and its all-input completeness theorem.
- `P1ResidualArithmetic.lean`: the parameter identity, congruences and power-sandwich theorem.
- `P1ResidualReach.lean`: formally proves exact G transcription inversion from Agent 1 and the full blank-reachable exclusion, importing the actual `ResetGate.lean`, `P1Triple.lean`, `P1ResidualArithmetic.lean`.

The sources compiled locally with Lean 4.36.0-rc2 against minimal exact transcriptions of the imported types and `G,T,Reach` definitions. Local proof `#print axioms` on the final theorem contained `propext,Classical.choice,Quot.sound` plus three **mock-only** axioms standing in for real Agent 1 proofs: `Agent1.even_left_power_shape, Agent1.reachable_even_mod4, Agent1.odd_parent_general`. These three names are real verified theorem declarations in the repository's source files. Therefore the local proof test validates theorem composition conditional on these imported facts; recompile with the repository's unmodified real source chain to discharge them completely.

Known strong upstream machine bridge: `im-results/agent19-p1-source-bridge/P1HaltingBridge.lean` and [manual CI run 41388451571](https://github.com/FlareZ123/bb6/actions/runs/41388451571).

**Next decisive target:** full local/CI integration with unmodified Agent 1 modules, import Agent 19's exact residual gateway, prove both reachability predicates equivalent (or use the common raw-machine bridge) and then attack the remaining `n≡2,6,14 (mod 16)` families. Beware earlier independent exclusion of the odd and multiple-of-four critical-index families.
