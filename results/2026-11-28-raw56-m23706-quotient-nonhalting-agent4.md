# Universal blank-tape nonhalting for the six-state M23706 one-hole family

*Original-source Lean 4.36.0-rc2 theorem accepted 28 November 2026: [CI 46135562496](https://github.com/FlareZ123/bb6/actions/runs/46135562496), final job 140962266922, source artifact [15261018092](https://github.com/FlareZ123/bb6/actions/runs/46135562496/artifacts/15261018092).*

## Theorem and original-machine semantics

For the standard blank-tape, two-symbol, six-state machine convention, fix the partial table

```
1RB1LC_1RC0LB_0RD0RF_1LD1LE_1RA1LB_---1RE
```

The only unspecified instruction is **state F reading symbol 0**. For **every** total six-state completion agreeing with the eleven literal transitions, the authentic blank-start execution never halts. The accepted Lean declaration is

```lean
BB6.Agent4Raw56RootE11LB.M23706Block.M23706.never
  (m : Machine) (hm : compatible table m) : NeverHalts m
```

The theorem is not conditional on a prepared tape, an unverified tail shape, a finite simulation cutoff, or a choice of the missing transition. It directly rules out all possible halting completions of this partial machine.

## Finite two-stack invariant

An asymmetric periodic-block compression builds a finite relation of 9,299 abstract control/read/left-stack/right-stack configurations with 194 left and 734 right automaton states. Context-congruent minimization quotients it to **4,653 joint configurations, 165 left and 353 right stack states**. Partition by the complete opposite-side context signature and refine to congruence for recorded push transitions; then independently re-enumerate all projected successors. The construction and proof of the reusable quotient principle are in [context-quotient.md](../im-results/agent4-two-sided-automata/context-quotient.md).

The **trusted proof boundary** is the unchanged `TwoSidedAutomata.check` checker. The twelve state/symbol row obligations each split into sixteen finite checking chunks and were compiled in separate Lean jobs. The final `M23706Final.lean` imports those verified row theorems and derives `M23706.never` through the original raw-machine semantic bridge. Its printed transitive axiom profile was exactly `[propext, Classical.choice, Quot.sound]`; there is no `sorryAx`, `native_decide`, or external oracle.

## Reproduction and significance

- Machine, unminimized fixed point and table: [m23706_block_cert.py](../im-results/agent4-raw56-root-pilot/m23706_block_cert.py).
- Size-pinned minimized relation: [m23706_min_cert.py](../im-results/agent4-raw56-root-pilot/m23706_min_cert.py), with [minimize_relation.py](../im-results/agent4-two-sided-automata/minimize_relation.py).
- Original-source Lean shard generator: [m_block_split.py](../im-results/agent4-raw56-root-pilot/m_block_split.py); [manual CI workflow](../.github/workflows/agent4-raw56-lb.yml) target `m23706` with `optimized=true`.
- Accepted artifact ZIP SHA-256: `5a80955723c30788753cb447bd4367d5ccf7fd6465502035856fea0296b05349`.

This resolves the last previously unaccepted **individual** residual in the 43,348-leaf Raw56 E1=1LB parent partition. All six such one-hole leaves now have individual original-source nonhalting proofs; the gigantic parent assembly and six-way consumer remain a distinct source-compilation obligation. Therefore the theorem does **not** yet certify the complete E1=1LB six-hole sibling, the full Raw56 branch, a global BB(6) upper bound, or the exact value of BB(6).
