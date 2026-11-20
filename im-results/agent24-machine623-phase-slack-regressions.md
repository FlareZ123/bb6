# Machine #623: phase/slack adversarial regression cases

**Purpose:** preserve known failures of reduced phase and slack invariants for the #623 S-window product work. These are negative tests for proposed abstractions, not a proof of root nonhalting or a universal classification. Distinguish finite root-trace observations from exact one-step source-arithmetic counterexamples.

## Leading ternary phase is not deterministic

Agent 24's source-transcribed root scan matched the recorded prefix for its first 17 states and examined 19,991 transitions after the first nine. Every one of the eight (sector, leading-high-digit) combinations occurred, and each had both observed successor sectors:

| Current sector | High digit | Observed successor sectors |
|---|---:|---|
| RO | 0 | LE, RE |
| RO | 1 | LE, RE |
| LE | 0 | LE, RE |
| LE | 1 | LE, RE |
| RE | 0 | RO, LO |
| RE | 1 | RO, LO |
| LO | 0 | RO, LO |
| LO | 1 | RO, LO |

A separate 5,000-step pass found the low-drain terminal state A exactly when the high digit was 0 and B exactly when it was 1; C did not occur. On this trace, the full terminal state therefore added no information beyond the leading high digit. Do not make the sector transition deterministic from (sector, high digit) alone.

Source: [Agent 24's original diagnostic](../../communications/agent49/20261120T075819Z_agent24-high-phase-not-sufficient.md). This is finite empirical evidence, not an all-time statement.

## Exact one-step slack counterexamples

These source-level transitions disprove several tempting state-local or residue-table preservation rules.

### H65 does not imply one-step cone preservation

The state D(18,88) has h=70, m=18, ceil(log_3(2m+1))=4, and slack 66. It satisfies the observed 65-slack inequality. The exact source equations give

```text
highLevelNext(D(18,88))
= drainB(71,18,41)
= D(70,65).
```

The output has h=5, m=65, slack 0 and lies outside newAffineCone. Thus the observed 65-slack condition is not a universal one-step preservation certificate.

Source: [Agent 27's exact counterexample](../../communications/broadcast/20261120T0630Z_agent27-h65-not-sufficient.md).

### Mod-3 class-specific slack thresholds fail

D(2,73) is right-odd, residues (2,1), slack 69, above the observed source-class minimum 65. Its exact next state is D(74,10), left-even residues (2,1), slack 61, below the target-class minimum 696153.

The authentic root state D(314,385) has the same source sector/residues (right-odd, (2,1)) and slack 65, but maps to D(74,950), right-even residues (2,2), slack 871. The source class therefore does not determine the target slack class.

Source: [Agent 27's residue-table failure](../../communications/agent32/20261120T0646Z_agent27-residue-slack-table-failure.md).

### Mod-9 class-specific slack thresholds fail

D(2,105) is right-odd, residues (2,6), slack 101, above the observed source-class minimum 96. Its exact next state is D(106,10), left-even residues (1,1), slack 93, below the target-class minimum 309. Increasing the residue modulus from 3 to 9 does not repair the finite-table invariant.

Source: [Agent 27's mod-9 failure](../../communications/agent32/20261120T0650Z_agent27-mod9-slack-table-failure.md).

## Related boundary regression

The earlier A-state macro note records a 2,000,000-step exact-tape replay in which, at step 23, state A has head -3 and the two cells immediately to its right are 00. This refutes the earlier two-sided “no adjacent 00” suffix claim; only the left-prefix observation remained. Do not reintroduce the withdrawn right-suffix condition.

Source: [Agent 24's A-state macro note](./agent24-machine623-macro-invariant.md).

## Existing required cases owned by the S-window project

Keep these separate tests in the same product/test harness:

- [Raw reset-language nonclosure](../agent32-623-phase-automaton/ClosureCounterexample.md): L start carry (-2,-2), input 00 02 00, output 11 02 10; R start carry (-4,-2), input 00 01 00, output 21 12 10.
- [Index-33 output-suffix counterexample](../agent32-623-phase-automaton/PhaseAutomaton.md): closure must apply to the whole next S-window, not an arbitrary suffix.

## Required interpretation

A proposed finite product or invariant must not:

1. infer a unique successor sector from (sector, leading high digit);
2. infer one-step cone preservation from the H65 inequality;
3. infer forward invariance from sector plus mod-3 or mod-9 residue-class slack minima;
4. restore the withdrawn two-sided no-00 suffix condition;
5. treat raw reset-language acceptance as invariant under either unconstrained branch transducer; or
6. close only an arbitrary suffix while ignoring the index-33 whole-window failure.

These cases are regression constraints on the proposed abstraction. They do not themselves provide the source-connected arithmetic restriction needed to exclude synthetic states or establish an all-time theorem.
