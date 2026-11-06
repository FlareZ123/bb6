# Cryptid D: source-certified return grammar and 3-adic synchronization

**Research state (6 November 2026): exact return and shift theorems for specified source configurations; no global true-blank halt/nonhalt decision.** [Complete working proof record](FULL_RESEARCH_LOG.md).

## Original machine and proven scope

The D-start table is `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`. The original `I_n(r)` F/0 section has blank left tape, leading unary `1^n) and suffix `r`. Physical blank-padding and first-return conditions matter when composing source steps.

- [BlankEighthRejoin.lean](BlankEighthRejoin.lean) source-certifies another actual-blank exceptional return after 6,046 regular source steps, with successful [original-source CI 41870046802](https://github.com/FlareZ123/bb6/actions/runs/41870046802). This is finite authentic continuation without a perpetual-survival conclusion.
- [DRegularShift.lean](DRegularShift.lean) proves for the canonical eleven-row regular return model, without the earlier conditional shift hypothesis, an all-depth `3^k` input/`8^k` output shift identity, including matching success and failure at regular exits. [CI 41872704046](https://github.com/FlareZ123/bb6/actions/runs/41872704046). [DRegularSourceShift.lean](DRegularSourceShift.lean) transports paired regular runs to the physical original six-state machine: [CI 41872968993](https://github.com/FlareZ123/bb6/actions/runs/41872968993).
- [DRegularDurationShift.lean](DRegularDurationShift.lean) and [DRegularTimedShift.lean](DRegularTimedShift.lean) give exact quadratic runtime dependence for `k` regular returns, with `55 Q_k + 12·9^k = 12·64^k`: [CI 41875379548](https://github.com/FlareZ123/bb6/actions/runs/41875379548). The physical-source timed composition and exceptional-packet extensions have their own dependencies, explained in the [full synthesis](2026-11-04-eighth-and-3adic-synchrony.md).
- Further source-certified lemmas describe a guarded E-boundary halting cylinder, B-run valuation, a universal **synthetic** unary halting extension, and precise E111 first-return conditions. All exact theorem references remain in the [full research log](FULL_RESEARCH_LOG.md).

## Unresolved root problem

Regular all-depth synchronization does not establish that the actual blank orbit remains regular at **every** return. Exceptional exits, physical suffix equivalence and possible original halts need complete treatment.

**Next proof:** establish a blank-root forward-closed word/suffix invariant across every exceptional packet, or produce an original-machine halting witness. A large finite trace or synthetic halting extension cannot settle the blank trajectory.
