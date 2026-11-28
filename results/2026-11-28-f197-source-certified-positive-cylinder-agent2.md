# F197: source-certified positive self-embedding of an unbounded blank-aligned cylinder

**28 November 2026.** This is an original-source Lean 4.36.0-rc2 theorem for a nontrivial infinite family of configurations of the six-state, two-symbol F197 machine
`1RB0RE_1RC0LE_0RD---_0RE0RA_1LF0LB_1LA1LF`.
It resolves the all-time nonhalting question for that family **without** imposing a bounded running time, periodicity of the full tape, or an artificially fixed right-hand tail. It does **not** by itself establish the theorem from the genuine blank tape, classify the whole Raw132 parent, or determine BB(6).

## Exact mathematical assertion

Use the literal Turing-machine semantics in [Macro.lean](../im-results/agent31-f197-macro/Macro.lean), where `B(a,e)` has state B, inclusive left tape `a`, and right tape `00e`; `e` is a one followed by zeros. Let the finite aligned words be

```
A = 10, T = 1100, J = 100, U = 11100
P = AAT
L = AATAAATAUJTT
HEAD = JTAATAAATATAATAATAATAATTATAATAATAATTAATTAAATAUJTT
```

The Lean theorem `F197.Agent2Self.self_embedding` asserts that **for every infinite left suffix** `l` whose leading bit is 1 there exists a strictly positive finite primitive-machine execution

```
B(P^72 HEAD L^35 l, e)  -->+  B(P^72 HEAD L^35 f(l), e).
```

Here `f` is an explicit guarded suffix transformer: in the checked proof it prepends seven `L` blocks, then `732592001087343536` additional `L` blocks, then `T` and a fixed finite marker continuation `Y`, before the unchanged `l`. Equivalently the `L` exponent in the prefix of `f(l)` is **732592001087343543**. Every such new suffix still starts with a 1. In particular, iterating this positive return yields a well-defined infinite execution of the literal F197 transition table for **every** configuration in this cylinder. Since `L=AATAAATAUJTT` has precisely **36 physical tape bits**, this source-certified return explicitly inserts **26,373,312,039,144,367,548 bits** just from its repeated `L` prefix, apart from the further `T` and finite marker word. This counts actual encoded tape bits, not macro steps; repetition yields an arbitrarily long growing prefix while the retained suffix is never inspected.

The stronger `F197.Agent2Self.self_nonhalt` proves directly:

```lean
∀ (l : Tape), l 0 = true →
  ∀ t : Nat, run t (state 72 START l) ≠ none
```

where `START = HEAD ++ flat L 35` and `state` prepends the indicated `P` power with the exact right-blank boundary. This all-time conclusion is **not** inferred merely from a long finite run: it follows by indefinitely composing the proved positive, suffix-parametric return.

## Proof architecture and accepted evidence

- Each finite local step is reduced to the original six-state literal transition rules, with explicit known-prefix/read guards. `Macro.lean` and [PrefixCheck.lean](../im-results/agent2-f197-sweep/PrefixCheck.lean) prove source-faithful interpretation for arbitrary untouched suffixes.
- Symbolic descent, terminal decoding, marker transfer, and reset cycles are established in the [EpochMarker/CounterCore/OrdinaryBulk family](../im-results/agent2-f197-sweep/README.md). The decisive trace has 3,765 local/ordinary transitions before a parity-controlled marker epoch and 256 after it. The marker multiplies the retained `L` reservoir without enumerating its 732-trillion-sized exponent.
- The [generators](../im-results/agent2-f197-sweep/generate_lean_trace.py) produce 658 distinct packed finite-operation checks and chunked source-specific Lean proof terms. Every operation bank is connected through the soundness theorem of [PackedCheck.lean](../im-results/agent2-f197-sweep/PackedCheck.lean); the final `SelfTheorem.lean` is generated reproducibly from the [exact checker](../im-results/agent2-f197-sweep/verify_nonhalt.py).
- **Original-source Lean acceptance:** [GitHub Actions run 46094555223](https://github.com/FlareZ123/bb6/actions/runs/46094555223), source commit `45965d2deb2360930b25be1e134d1ce741be34a9`. The entire `self_embedding`/`self_nonhalt` dependency closure compiled using pinned Lean 4.36.0-rc2 and printed only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`. The separately run [exact independent Python certificate check](https://github.com/FlareZ123/bb6/actions/runs/46094784084) also passed.

The original stand-alone computational proof used a **narrower** cylinder with `L^80`; the source-certified theorem strengthens its starting family to `L^35`. The reconstructed source code and integer parameters are sufficient to replay the proof; no finite-only liveness assertion is silently promoted to an infinite claim.

## Scope toward BB(6)

The actual blank-tape trajectory has a separate exact *computational* certificate reaching `B(P^72 HEAD L^80 l,e)` after 5,810,803 primitive seed transitions and accelerated epochs, described in [NonhaltingCertificate.md](../im-results/agent2-f197-sweep/NonhaltingCertificate.md). Its full generated `RootTheorem.blank_nonhalt` had **not** been source accepted when this result was written. That root bridge, the original integer-tape-compatible weighted `Cover`, and complete Raw132/global quotient consumption are logically distinct obligations. The theorem reported here discharges the difficult infinite-cylinder liveness quantifier without claiming those missing edges.
