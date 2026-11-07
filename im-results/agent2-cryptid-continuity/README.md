# Cryptid D: source-certified return grammar and 3-adic synchronization

**Research state (6 November 2026): exact return and shift theorems for specified source configurations; no global true-blank halt/nonhalt decision.** [Complete working proof record](FULL_RESEARCH_LOG.md).

## Original machine and proven scope

The D-start table is `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`. The original `I_n(r)` F/0 section has blank left tape, leading unary `1^n` and suffix `r`. Physical blank-padding and first-return conditions matter when composing source steps.

- [BlankEighthRejoin.lean](BlankEighthRejoin.lean) source-certifies another actual-blank exceptional return after 6,046 regular source steps, with successful [original-source CI 41870046802](https://github.com/FlareZ123/bb6/actions/runs/41870046802). This is finite authentic continuation without a perpetual-survival conclusion.
- [DRegularShift.lean](DRegularShift.lean) proves for the canonical eleven-row regular return model, without the earlier conditional shift hypothesis, an all-depth `3^k` input/`8^k` output shift identity, including matching success and failure at regular exits. [CI 41872704046](https://github.com/FlareZ123/bb6/actions/runs/41872704046). [DRegularSourceShift.lean](DRegularSourceShift.lean) transports paired regular runs to the physical original six-state machine: [CI 41872968993](https://github.com/FlareZ123/bb6/actions/runs/41872968993).
- [DRegularDurationShift.lean](DRegularDurationShift.lean) and [DRegularTimedShift.lean](DRegularTimedShift.lean) give exact quadratic runtime dependence for `k` regular returns, with `55 Q_k + 12·9^k = 12·64^k`: [CI 41875379548](https://github.com/FlareZ123/bb6/actions/runs/41875379548). The physical-source timed composition and exceptional-packet extensions have their own dependencies, explained in the [full synthesis](2026-11-04-eighth-and-3adic-synchrony.md).
- Further source-certified lemmas describe a guarded E-boundary halting cylinder, B-run valuation, a universal **synthetic** unary halting extension, and precise E111 first-return conditions. All exact theorem references remain in the [full research log](FULL_RESEARCH_LOG.md).

## Unresolved root problem

Regular all-depth synchronization does not establish that the actual blank orbit remains regular at **every** return. Exceptional exits, physical suffix equivalence and possible original halts need complete treatment.

**Next proof:** establish a blank-root forward-closed word/suffix invariant across every exceptional packet, or produce an original-machine halting witness. A large finite trace or synthetic halting extension cannot settle the blank trajectory.


## Exact 3-adic block evaluation for long regular runs (7 November 2026)

**DRegularFast.lean** turns the all-depth shift theorem in **DRegularShift.run_shift** into an exact block evaluator. For a canonical section s and block length k, write

    s.a = 2 + ((s.a-2) mod 3^k) + 3^k * ((s.a-2) / 3^k).

The small representative is evaluated for k regular sections. The exact shift theorem lifts its endpoint by 8^k times the quotient. The file proves **run_block**, the multi-block evaluator **fastRunBlocks**, and the arbitrary-length identity

    DRegular.run n s = DRegularFast.fastRun n s.

The current block size is 512. This is an exact evaluator for the eleven-row DRegular model, not a new theorem about the original machine.

**Local validation (Lean 4.36.0-rc2):** a standalone kernel computation evaluated the 12,588-step twenty-first regular segment from the actual symbolic-root seed, represented as a 116,926-bit integer (SHA-256 6058f62d1da9808c0da7609037f59cfe61fba7ceadf9dc0886dfbc25d66b9781). It produced the 134,738-bit endpoint (SHA-256 3e2c1a9d3ca8c6b80cd32917a32601966814ec5f0718f48ff6dc2ff60fbbf767), with shape L(9*t21+4,8,1) and t21 mod 27 = 6. The explicit fastRun computation plus endpoint check compiled in 9.36 seconds with 1.5 GB maximum RSS; the endpoint computation itself is by decide and has no axioms. The generic equality theorem inherits the axiom profile of DRegularShift.run_shift ([propext, Classical.choice, Quot.sound]).

**BlankTwentyFirstRejoin.lean** now uses DRegularFast.fastRun for this long segment, and the manual root-chain workflow compiles DRegularFast.lean before it. The earlier root-chain run [42377931873](https://github.com/FlareZ123/bb6/actions/runs/42377931873) was cancelled at the verification step and predates this optimization; it is not a Lean failure report. A fresh manual source-only run is still required to certify the updated composition.

## Corrected conditional root lookahead: first residual at exception 41

A second continuation pass now uses the **source-specific E7 branches** (EEE escape, E/E packet, and third-return cases), rather than applying the generic two-return arithmetic formula to every E7 state. This corrects the earlier exploratory claim of a clean lookahead through exception 100: that claim was invalid for E7 states with q >= 3 and must be disregarded.

Conditional on the existing root-20/21/22 reentries, the exact DRegular model reaches the first currently uncovered p=2 reset at exception **#41**:

- Exceptional section: L(9*t41+7, 7, 1), with t41 mod 81 = 76 (hence t41 mod 27 = 22).
- The source-specific EEE escape uses u41=(t41-1)/3, with u41 mod 27 = 25 and u41 mod 9 = 7.
- It produces the packet M(512*u41+257, 4, 2; 0 1^6). Its prefix is 1 mod 3, so this is an E,p=2 reset, not an A-packet closure.
- The reset parameter is k41=(512*u41+257-4)/3, with k41 mod 81 = 76 and **k41 mod 9 = 4**.
- The p=2 reset output has q=4 and p=14 in the reset marker, with the fixed marker word 01010111. The existing source families cover k mod 3 = 0, k mod 3 = 2, and k mod 9 = 1. They do not cover k mod 9 = 4.

The first residual is therefore a **reachable k = 4 mod 9 p=2 marker**, conditional on the upstream blank-root chain. This is the next source-level target. The k=7 mod 9 class remains a separate general residual; this run has not established whether it is also reachable.

The corrected arithmetic trace from exceptions 21 through 40 uses the already-developed B/A/E return families and the source-specific E7 packet normalization. The first 20 steps of that continuation contain no uncovered p=2 reset; exception 41 is the first one. These are model-level computations and proposed source compositions, not an original-source proof of the full blank-root chain. The upstream root-chain workflow [42377931873](https://github.com/FlareZ123/bb6/actions/runs/42377931873) was cancelled at its verification step and predates the DRegularFast optimization; a fresh manual source-only run is still needed.

The exact reset arithmetic can be reproduced from the DRegular model. Useful residues for adversarial checking are:

| Quantity | Exact residue |
|---|---:|
| t41 mod 81 | 76 |
| u41 mod 27 | 25 |
| (512*u41+257) mod 81 | 70 |
| k41 mod 81 | 76 |
| k41 mod 9 | **4** |
| (8*k41+5) mod 81 | 46 |

Do not use the earlier #44/#45/#58/#64/#68/#78/#82/#90/#92/#93/#100 continuation table as evidence: it came from the incorrect E7 shortcut and has been superseded by this corrected branch analysis.
