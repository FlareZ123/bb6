# Historical rooted #119: exact auxiliary halting gate and conditional tape shields

**Research state (6 November 2026): exact auxiliary-machine gate proofs and scoped physical sweep laws; a universal authentic blank-start decision is missing.** [Complete source formulas, experiments, and dated proofs](FULL_RESEARCH_LOG.md).

## Which machine is analyzed?

The historical #119 root `1RB1LB_1RC---_1LD1LF_1LE0LD_0LA1RF_1LC0RE` has an already known BusyCoq equivalence to auxiliary root `1RB---_1LC1LF_1LD0LC_0LE1RF_1RA1LA_1LB0RD`. The equivalence and independently sampled raw configuration merger are discussed in the [source provenance dossier](../agent12-r001-source/README.md). This work studies the auxiliary's unique undefined A/1 rule.

[Root119Gate.lean](Root119Gate.lean) defines a direct physical small-step semantics on an infinite signed tape and proves `BB6Root119.blank_halts_iff_gate`: auxiliary blank halting occurs **iff** an actually reached D/0 state has two consecutive 1 cells immediately to the left. The all-time proof is locally kernel checked over the stated transition table; the original BusyCoq/Lean import bridge and independent external novelty remain separate questions.

## Additional exact statements

The detailed note proves or examines source-shaped alternating B/0 sweeps, D/F rightward laws for arbitrary blocks, and an F/1 forward-and-back wave with a one-bit return normal form. These are conditional transition facts with specific entry shields. Numerical falsification includes up to 50 million raw steps and smaller synthetic cases. The finite runs are evidence for debugging, not a machine-wide result.

## What remains

Prove that the auxiliary blank orbit obeys a source-sound, phase-complete tape shield for **every** potential D/0 halting gate, including alternate B/0 returns; or find a genuine reachable gate. Temporary forbidden factors can appear inside a phase and disappear before the next return, so any invariant must specify the observation point precisely.

The [full research log](FULL_RESEARCH_LOG.md) preserves exact local proof status, guards, falsifiers, byte-level reproduction and all conditional wave formulas.
